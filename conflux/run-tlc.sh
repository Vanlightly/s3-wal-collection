#!/usr/bin/env bash
set -euo pipefail

# Set TLA2TOOLS_JAR and COMMUNITY_MODULES_JAR to the installed jars.
# Run the task modules composed through EXTENDS.
# --check: small exhaustive Java/TLA+ equivalence and safety check.
# --quick: two replicas and values, one slot per loglet, two loglets.
# --pure: use only the TLA+ definitions; --build-only: build the Toolbox jar.
# Remaining arguments are passed to TLC, e.g. -coverage 1 or -config file.cfg.
root_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
spec_dir="$root_dir/spec"
use_java=true
build_only=false
model_kind=
while (($#)); do
    case "$1" in
        --pure) use_java=false; shift ;;
        --check) model_kind=Check; shift ;;
        --quick) model_kind=Quick; shift ;;
        --build-only) build_only=true; shift ;;
        *) break ;;
    esac
done
module="$spec_dir/Conflux.tla"
config="Conflux$model_kind"
if [[ "$model_kind" == Check ]]; then
    module="$root_dir/ConfluxCheck.tla"
fi

: "${TLA2TOOLS_JAR:?Set TLA2TOOLS_JAR to the path of tla2tools.jar}"
: "${COMMUNITY_MODULES_JAR:?Set COMMUNITY_MODULES_JAR to the CommunityModules jar}"
for jar in "$TLA2TOOLS_JAR" "$COMMUNITY_MODULES_JAR"; do
    if [[ ! -f "$jar" ]]; then
        printf 'Jar not found: %s\n' "$jar" >&2
        exit 1
    fi
done

classpath="$TLA2TOOLS_JAR:$COMMUNITY_MODULES_JAR"
if "$use_java"; then
    mkdir -p "$root_dir/.tlc-classes"
    javac --release 11 -cp "$TLA2TOOLS_JAR" -d "$root_dir/.tlc-classes" \
        "$root_dir/ConfluxCommon.java"
    override_jar="$root_dir/.tlc-classes/Conflux-overrides.jar"
    jar --create --file "$override_jar" \
        -C "$root_dir/.tlc-classes" ConfluxCommon.class \
        -C "$root_dir/.tlc-classes" 'ConfluxCommon$Cache.class'
    classpath="$override_jar:$classpath"
fi
if "$build_only"; then
    if "$use_java"; then
        printf 'Toolbox override jar: %s\n' "$override_jar"
    fi
    exit 0
fi

run_dir=$(mktemp -d "${TMPDIR:-/tmp}/conflux-tlc.XXXXXXXX")
tlc_pid=
cleanup() {
    if [[ -n "$tlc_pid" ]]; then
        kill "$tlc_pid" 2>/dev/null || true
        wait "$tlc_pid" 2>/dev/null || true
    fi
    rm -rf -- "$run_dir"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
java -XX:+UseParallelGC "-Xmx${TLC_HEAP:-8g}" "-DTLA-Library=$spec_dir" \
    -cp "$classpath" tlc2.TLC \
    -noGenerateSpecTE -workers "${TLC_WORKERS:-8}" \
    -metadir "$run_dir/states" -config "$root_dir/$config.cfg" \
    "$@" "$module" &
tlc_pid=$!
wait "$tlc_pid"
tlc_pid=
