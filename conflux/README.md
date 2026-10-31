# Conflux specification

The core TLA+ modules live in [spec/](./spec/). The main [Conflux.tla](./spec/Conflux.tla) uses task modules for Apply, Append, GC, and Reconf, with one operation record per task and one [ConfluxCommon.tla](./spec/ConfluxCommon.tla) for constants, helpers, and state declarations. See [Conflux_notes.md](./Conflux_notes.md) for the algorithm, data model, and transition diagrams.

[ConfluxCheck.tla](./ConfluxCheck.tla), the model `.cfg` files, and the Java override remain in `conflux/`, separate from the spec. The launcher adds `spec/` to TLC's module search path so the check module can import the spec.

Set `TLA2TOOLS_JAR` and `COMMUNITY_MODULES_JAR` to the installed TLC and CommunityModules jars before using the launcher.

The launcher supports `--pure`, `--quick`, `--check`, and `--build-only`. Use `--check` for safety and reconstruction checks. By default, it compiles [ConfluxCommon.java](./ConfluxCommon.java) into `conflux/.tlc-classes/Conflux-overrides.jar` and uses its reconstruction override. `--pure` uses only the TLA+ definitions; `--build-only` builds the override archive without running TLC. Remaining arguments are passed to TLC.

## Running the task-based spec

From the repository root:

```sh
conflux/run-tlc.sh --check        # Small safety and Java/TLA+ reconstruction check
conflux/run-tlc.sh --pure --check # Same model without the Java override
conflux/run-tlc.sh --quick        # Two replicas/values, one slot per loglet
conflux/run-tlc.sh                # Two replicas/values, two slots per loglet
```

The configurations check safety. Select `LivenessSpec` and the desired temporal properties to check reconfiguration and prefix-trim completion; omit symmetry for liveness checking.

## Toolbox

Open [spec/Conflux.tla](./spec/Conflux.tla) as the root and use [Conflux.cfg](./Conflux.cfg) as the model-settings guide. Include the CommunityModules jar in the spec's library settings. To open `ConfluxCheck.tla` as a separate root, also add the absolute path to `conflux/spec` as a library directory. The active saved model binds `RECEIVE_TAIL` and `REFRESH_AFTER_MISSING` and selects `ValidApplyState`; custom models need those settings too. Reparse after changing the spec.

To use the Java reconstruction override, run `conflux/run-tlc.sh --build-only` and add `conflux/.tlc-classes/Conflux-overrides.jar` to the Toolbox library settings. The raw TLC output should report `Loading ReconstructLog operator override` from `ConfluxCommon.class`.
