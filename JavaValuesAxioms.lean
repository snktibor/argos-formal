import JavaRecordUpdate

-- Pin the axiom dependencies of the value encoding and record-update subset.

/-- info: 'Argos.JavaValues.unit_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.unit_valid

/-- info: 'Argos.JavaValues.unit_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.unit_code

/-- info: 'Argos.JavaValues.unit_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.unit_injective

/-- info: 'Argos.JavaValues.sentinel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.sentinel

/-- info: 'Argos.JavaValues.nonnull_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.nonnull_injective

/-- info: 'Argos.JavaValues.nullable_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.nullable_injective

/-- info: 'Argos.JavaValues.empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.empty

/-- info: 'Argos.JavaValues.nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.nonempty

/-- info: 'Argos.JavaValues.equality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.equality

/-- info: 'Argos.JavaValues.nullable_equality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.nullable_equality

/-- info: 'Argos.JavaValues.length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Argos.JavaValues.length

/-- info: 'Argos.JavaValues.null_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.null_distinct

/-- info: 'Argos.JavaValues.trim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.trim

/-- info: 'Argos.JavaValues.normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.normalized

/-- info: 'Argos.JavaValues.trim_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.trim_nonempty

/-- info: 'Argos.JavaValues.image_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.image_injective

/-- info: 'Argos.JavaValues.fields' does not depend on any axioms -/
#guard_msgs in
#print axioms Argos.JavaValues.fields

/-- info: 'Argos.JavaValues.increment' does not depend on any axioms -/
#guard_msgs in
#print axioms Argos.JavaValues.increment

/-- info: 'Argos.JavaValues.unit_trim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.unit_trim

/-- info: 'Argos.JavaValues.trim_predicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.trim_predicate

/-- info: 'Argos.JavaValues.normal_update_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Argos.JavaValues.normal_update_eq

/-- info: 'Argos.JavaValues.normal_update_image' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Argos.JavaValues.normal_update_image

/-- info: 'Argos.JavaValues.normal_update_version_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.normal_update_version_bounds

/-- info: 'Argos.JavaValues.normal_update_refines_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.JavaValues.normal_update_refines_apply
