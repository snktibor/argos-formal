import JavaValues

namespace Argos.JavaValues

theorem unit_valid : UnitValidSpec := by
  intro u
  have bound := UInt16.toNat_lt_size u
  change u.toNat < 65536 at bound
  unfold scalar Char.isValidCharNat
  by_cases h : u.toNat ≤ 32
  · rw [if_pos h]
    exact Or.inl (by omega)
  · rw [if_neg h]
    exact Or.inr ⟨by omega, by omega⟩

theorem unit_code : UnitCodeSpec := by
  intro u
  unfold unit Char.ofNat
  rw [dif_pos (unit_valid u)]
  rfl

theorem unit_injective : UnitInjectiveSpec := by
  intro a b h
  have codes := congrArg Char.toNat h
  rw [unit_code a, unit_code b] at codes
  apply UInt16.toNat_inj.mp
  unfold scalar at codes
  split at codes <;> split at codes <;> omega

theorem sentinel : SentinelSpec := by
  intro u h
  have codes := congrArg Char.toNat h
  rw [unit_code u] at codes
  change scalar u = 33 at codes
  unfold scalar at codes
  split at codes <;> omega

theorem nonnull_injective : NonnullInjectiveSpec := by
  intro a b h
  exact (List.map_inj_right unit_injective).mp (congrArg String.data h)

theorem null_distinct : NullDistinctSpec := by
  intro s h
  have chars := congrArg String.data h
  cases s with
  | nil => cases chars
  | cons u us =>
    have head : Char.ofNat 33 = unit u := (List.cons.inj chars).1
    exact sentinel u head.symm

theorem nullable_injective : NullableInjectiveSpec := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (null_distinct b h)
  | some a =>
    cases b with
    | none => exact False.elim (null_distinct a h.symm)
    | some b => exact congrArg some (nonnull_injective a b h)

theorem empty : EmptySpec := by
  intro s
  constructor
  · intro h
    exact nonnull_injective s [] h
  · intro h
    subst s
    rfl

theorem nonempty : NonemptySpec := by
  intro s
  exact not_congr (empty s)

theorem equality : EqualitySpec := by
  intro a b
  exact ⟨nonnull_injective a b, congrArg nonnull⟩

theorem nullable_equality : NullableEqualitySpec := by
  intro a b
  exact ⟨nullable_injective a b, congrArg nullable⟩

theorem length : LengthSpec := by
  intro s
  simp [nonnull]

theorem unit_trim (u : UInt16) : ((unit u).toNat ≤ 32) ↔ u.toNat ≤ 32 := by
  rw [unit_code u]
  unfold scalar
  by_cases h : u.toNat ≤ 32
  · rw [if_pos h]
  · rw [if_neg h]
    constructor <;> intro contra <;> omega

theorem trim_predicate :
    (fun c : Char => decide (c.toNat ≤ 32)) ∘ unit =
      (fun u : UInt16 => decide (u.toNat ≤ 32)) := by
  funext u
  simp [unit_trim]

theorem trim : TrimSpec := by
  intro s
  unfold javaTrim nonnull trimUnits
  change String.mk ((((s.map unit).dropWhile (fun c => c.toNat ≤ 32)).reverse.dropWhile
    (fun c => c.toNat ≤ 32)).reverse) = _
  simp only [List.dropWhile_map, trim_predicate, ← List.map_reverse]

theorem normalized : NormalizedSpec := by
  intro s
  rw [trim s]
  exact equality _ _

theorem trim_nonempty : TrimNonemptySpec := by
  intro s
  rw [trim s]
  exact nonempty _

theorem image_injective : ImageInjectiveSpec := by
  intro a b h
  have hi := nullable_injective _ _ (congrArg Image.id h)
  have ha := nullable_injective _ _ (congrArg Image.accumulator h)
  have hv : a.version = b.version := congrArg Image.version h
  have hc := nullable_injective _ _ (congrArg Image.created h)
  have hu := nullable_injective _ _ (congrArg Image.updated h)
  cases a
  cases b
  simp_all

theorem fields : FieldsSpec := by
  intro r
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem increment : IncrementSpec := by
  intro r a t
  rfl

end Argos.JavaValues
