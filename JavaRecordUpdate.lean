import ArgosGuard
import JavaValuesProofs

namespace Argos.JavaValues

def maxLong : Int := 9223372036854775807

/-- The value-level normal-return contract of a successful record update.
This predicate is a premise, not a model of Java execution or a validator. -/
structure NormalUpdate (before after : RawRecord) (a t : JavaString) : Prop where
  version_nonnegative : 0 ≤ before.version
  version_capacity : before.version < maxLong
  version_increment : after.version = before.version + 1
  id_preserved : after.id = before.id
  created_preserved : after.created = before.created
  accumulator_updated : after.accumulator = some a
  timestamp_updated : after.updated = some t

theorem normal_update_eq (before after : RawRecord) (a t : JavaString)
    (h : NormalUpdate before after a t) : after = updateRaw before a t := by
  cases before
  cases after
  cases h
  simp_all [updateRaw]

theorem normal_update_image (before after : RawRecord) (a t : JavaString)
    (h : NormalUpdate before after a t) :
    image after =
      { image before with
        accumulator := nonnull a
        version := before.version + 1
        updated := nonnull t } := by
  rw [normal_update_eq before after a t h]
  exact increment before a t

theorem normal_update_version_bounds (before after : RawRecord) (a t : JavaString)
    (h : NormalUpdate before after a t) :
    0 < after.version ∧ after.version ≤ maxLong := by
  have := h.version_nonnegative
  have := h.version_capacity
  have := h.version_increment
  omega

abbrev RecordState := Key → RawRecord

def versions (s : RecordState) : State := fun k => (s k).version.toNat

def replaceRecord (s : RecordState) (target : Key) (after : RawRecord) : RecordState :=
  fun k => if k = target then after else s k

/-- A single successful record replacement agrees with the existing Argos
write transition after projecting record values to natural-number versions.
This does not establish endorsement, MVCC validation, or Java call coverage. -/
theorem normal_update_refines_apply (s : RecordState) (tx : Tx) (target : Key)
    (after : RawRecord) (a t : JavaString)
    (writes : tx.writes = [target]) (h : NormalUpdate (s target) after a t) :
    versions (replaceRecord s target after) = Argos.apply (versions s) tx := by
  funext k
  by_cases hk : k = target
  · subst k
    simp only [versions, replaceRecord, Argos.apply, writes]
    simp only [List.mem_singleton, ↓reduceIte]
    have hn := h.version_nonnegative
    have hi := h.version_increment
    rw [hi, Int.toNat_add hn (by decide)]
    rfl
  · simp [versions, replaceRecord, Argos.apply, writes, hk]

end Argos.JavaValues
