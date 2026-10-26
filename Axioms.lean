/-
  The axioms each main theorem depends on. `#guard_msgs` fails the build if
  the list changes, so `lake build` rejects `sorry` (`sorryAx`), `native_decide`
  (`Lean.ofReduceBool`) and any custom axiom behind these theorems.
  A toolchain update can change the list, because `simp` may pick other lemmas.
-/
import ArgosGuard
import ArgosGuardExt
import ArgosToctou

-- ArgosGuard.lean
/-- info: 'Argos.at_most_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.at_most_one
/-- info: 'Argos.at_most_one_from_checked_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.at_most_one_from_checked_state
/-- info: 'Argos.rejected_detectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Argos.rejected_detectable
/-- info: 'Argos.b1u_both_commit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.b1u_both_commit
/-- info: 'Argos.stale_never_commits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.stale_never_commits

-- ArgosGuardExt.lean
/-- info: 'Argos.committed_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.committed_append
/-- info: 'Argos.version_grows_has_writer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.version_grows_has_writer
/-- info: 'Argos.writer_bumps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.writer_bumps
/-- info: 'Argos.rejected_has_prior_committed_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Argos.rejected_has_prior_committed_writer
/-- info: 'Argos.guard_excludes_prior_writer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.guard_excludes_prior_writer
/-- info: 'Argos.at_most_one_via_one_sided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.at_most_one_via_one_sided
/-- info: 'Argos.pair_alone_exactly_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.pair_alone_exactly_one
/-- info: 'Argos.mutuallyGuarded_of_endorse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.mutuallyGuarded_of_endorse
/-- info: 'Argos.at_most_one_endorsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.at_most_one_endorsed
/-- info: 'Argos.b1u_endorsed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.b1u_endorsed

-- ArgosToctou.lean
/-- info: 'Argos.tas_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.tas_spec
/-- info: 'Argos.window_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.window_closed
/-- info: 'Argos.check_holds_at_use' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.check_holds_at_use
/-- info: 'Argos.no_bifurcation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.no_bifurcation
/-- info: 'Argos.toctou_attack_unguarded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Argos.toctou_attack_unguarded
