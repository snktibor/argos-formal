# Java values and a single-record update

This subset proves a value-level refinement to the existing `Argos.apply` model. The Java-execution premise remains open.

## Checked statements

All names below are in `Argos.JavaValues`.

- `JavaValuesProofs.lean` proves 18 specified properties: code-unit validity and injectivity, null separation, string equality/emptiness/length, trim commutation, and complete record-image preservation.
- `normal_update_eq` shows that an update satisfying `NormalUpdate` equals `updateRaw` on all five fields.
- `normal_update_image` preserves ID and creation metadata, sets accumulator and update timestamp, and increments the version in the encoded image.
- `normal_update_version_bounds` proves the resulting version is positive and at most Java's signed `long` maximum.
- `normal_update_refines_apply` proves:

```lean
versions (replaceRecord s target after) = Argos.apply (versions s) tx
```

Its premises are `tx.writes = [target]` and `NormalUpdate (s target) after a t`. `replaceRecord` changes only the selected record. `versions` projects each integer version with `Int.toNat`; the updated record must start nonnegative. The theorem does not require or establish global well-formedness of other records.

## Representation

A `JavaString` is an ordered list of UTF-16 code units, including unpaired surrogates. Code units at most 32 keep their values; every other code unit is mapped to the Unicode scalar `65536 + unit`. This is an injective proof encoding, not UTF-8 serialization or human-readable decoding. Its Lean character count equals the original code-unit count.

Nullable strings use a separate sentinel, scalar 33, which cannot occur in an encoded nonnull string. Thus null, the empty string and the Java string `"!"` remain distinct. The sentinel is nonempty and trim-stable: encoded nonemptiness alone does not establish Java nonnullness.

`javaTrim` removes values at most 32 from both ends, matching the code-unit operation formalized by `trimUnits`. `RawRecord` and `Image` retain ID, accumulator, signed version, creation metadata and update metadata; metadata may be null.

## Premises and remaining connection

`NormalUpdate` assumes the exact value-level effects of a successful update: the original version is between zero and `maxLong - 1`, the new version is one greater, ID and creation metadata are preserved, and accumulator/timestamp are assigned the supplied nonnull values. This predicate is not an execution semantics or a proof about Java source.

The missing implementation obligation is to show that every actual successful Java call produces those captured values and effects. This PR supplies no Java/KeY proof import and no executable Java changes. Guard observations, validation, ownership/authentication, rejection, heap capture, physical codecs, Fabric behavior and MVCC/read-set correspondence are outside this subset. The theorem does not extend the existing protocol safety results to the implementation by itself.

## Reproducing the checks

Use the pinned Lean 4.23.0 toolchain:

```sh
lake build --wfail
for module in JavaValues JavaValuesProofs JavaRecordUpdate JavaValuesAxioms; do
  lake env lean --trust=0 "$module.lean" || exit 1
done
./mutations/check.sh
```

`JavaValuesAxioms.lean` uses `#guard_msgs` to pin every exported theorem's axiom inventory, including two auxiliary lemmas. Dependencies are limited to Lean's `propext`, `Quot.sound` and, for the arithmetic bounds theorem, `Classical.choice`. No `sorry`, custom axioms or `native_decide` are used.
