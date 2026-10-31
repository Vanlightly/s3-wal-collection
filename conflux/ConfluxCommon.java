import tlc2.value.impl.FunctionValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

/** Optional, pure TLC override. The reference operator is in spec/ConfluxCommon.tla. */
public final class ConfluxCommon {
    private ConfluxCommon() { }

    private static final StringValue LOGLETS = new StringValue("loglets");
    private static final StringValue FIRST = new StringValue("first");
    private static final StringValue ID = new StringValue("id");
    private static final StringValue TAIL = new StringValue("tail");
    private static final StringValue TRIM = new StringValue("trimIndex");
    private static final StringValue SNAPSHOT = new StringValue("snapshot");

    // TLC values are immutable in meaning. Reuse the result only when all
    // five argument objects are identical; no hashing or state fingerprints.
    // One entry per worker bounds retention and avoids shared mutable state.
    private static final class Cache {
        Value manifest, objects, checkpoints, unwritten, maxLength, result;
    }
    private static final ThreadLocal<Cache> CACHE = ThreadLocal.withInitial(Cache::new);

    private static Value field(Value record, StringValue name) {
        return ((RecordValue) record).select(name);
    }

    private static int number(Value value) {
        return ((IntValue) value).val;
    }

    private static Value at(Value function, Value key) {
        return ((FunctionValue) function).apply(key, 0);
    }

    public static Value ReconstructLog(Value manifest, Value objects,
            Value checkpoints, Value unwritten, Value maxLength) {
        Cache cache = CACHE.get();
        if (cache.manifest == manifest && cache.objects == objects
                && cache.checkpoints == checkpoints && cache.unwritten == unwritten
                && cache.maxLength == maxLength) {
            return cache.result;
        }
        Value[] loglets = ((TupleValue) field(manifest, LOGLETS).toTuple()).elems;
        Value active = loglets[loglets.length - 1];
        int first = number(field(active, FIRST));
        int trim = number(field(manifest, TRIM));
        int limit = number(maxLength);
        int tail = Math.max(1, trim - first + 2);
        Value activeEntries = at(objects, field(active, ID));
        while (tail <= limit && !at(activeEntries, IntValue.gen(tail)).equals(unwritten)) {
            tail++;
        }
        // FirstMissing returns the sentinel even if the scan starts beyond it.
        tail = Math.min(tail, limit + 1);
        Value[] result = new Value[Math.max(0, first + tail - 2)];
        Value snapshot = trim > 0 ? at(checkpoints, field(manifest, SNAPSHOT)) : null;
        for (int index = 1; index <= result.length; index++) {
            if (index <= trim) {
                result[index - 1] = at(snapshot, IntValue.gen(index));
                continue;
            }
            Value selected = null;
            for (Value loglet : loglets) {
                int start = number(field(loglet, FIRST));
                int end = number(field(loglet, TAIL));
                if (start <= index && (end == 0 || index < start + end - 1)) {
                    // TLC's CHOOSE enumerates the set in canonical value order.
                    if (selected == null || loglet.compareTo(selected) < 0) {
                        selected = loglet;
                    }
                }
            }
            if (selected == null) {
                throw new IllegalArgumentException("No loglet covers index " + index);
            }
            int slot = index - number(field(selected, FIRST)) + 1;
            result[index - 1] = at(at(objects, field(selected, ID)), IntValue.gen(slot));
        }
        cache.manifest = manifest;
        cache.objects = objects;
        cache.checkpoints = checkpoints;
        cache.unwritten = unwritten;
        cache.maxLength = maxLength;
        cache.result = new TupleValue(result);
        return cache.result;
    }
}
