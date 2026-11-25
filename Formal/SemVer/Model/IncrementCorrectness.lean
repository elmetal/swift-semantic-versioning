import SemVer.Model.Increment
import SemVer.Model.Correctness
import SemVer.Theorems.Increment

/-!
# 繰り上げの実装モデルの正しさ

主定理:

* `succDigits_spec`: 数値識別子に `succDigits` を適用すると、数値識別子のまま値が 1 増える。
* `Components.toVersion_nextPatch` ほか: 妥当な構成要素について、バイト列のままの繰り上げは
  仕様の繰り上げと一致する。
* `Components.nextPatch_spec` ほか: したがって結果は「その種類のリリースのうち、元より高くて最も低いもの」である。
-/

namespace SemVer

open Spec

/-! ## 数字 1 文字に 1 を足す -/

theorem Spec.IsDigit.succ_toNat {c : Byte} (h : IsDigit c) : (c + 1).toNat = c.toNat + 1 := by
  have hb := h.toNat_bounds
  have e : (1 : Byte).toNat = 1 := rfl
  rw [UInt8.toNat_add, e]
  omega

theorem Spec.IsDigit.succ_isPositiveDigit {c : Byte} (h : IsDigit c) (hc : c ≠ 0x39) :
    IsPositiveDigit (c + 1) := by
  have hb := h.toNat_bounds
  have hs := h.succ_toNat
  have hne : c.toNat ≠ 57 := fun e => hc (UInt8.toNat_inj.mp e)
  have e₁ : (0x31 : UInt8).toNat = 49 := rfl
  have e₂ : (0x39 : UInt8).toNat = 57 := rfl
  exact And.intro (UInt8.le_iff_toNat_le.mpr (by omega)) (UInt8.le_iff_toNat_le.mpr (by omega))

theorem Spec.IsDigit.succ_digitValue {c : Byte} (h : IsDigit c) :
    digitValue (c + 1) = digitValue c + 1 := by
  have hb := h.toNat_bounds
  have hs := h.succ_toNat
  have e : Ascii.zero.toNat = 48 := rfl
  unfold digitValue
  omega

/-! ## `succAux` の場合ごとの値 -/

theorem succAux_cons_carry_nine {cs : List Byte} (hr : (succAux cs).2 = true) :
    succAux ((0x39 : Byte) :: cs) = (Ascii.zero :: (succAux cs).1, true) := by
  simp [succAux, hr]

theorem succAux_cons_carry {c : Byte} {cs : List Byte} (hr : (succAux cs).2 = true)
    (hc : c ≠ 0x39) : succAux (c :: cs) = ((c + 1) :: (succAux cs).1, false) := by
  simp [succAux, hr, hc]

theorem succAux_cons_noCarry {c : Byte} {cs : List Byte} (hr : ¬ (succAux cs).2 = true) :
    succAux (c :: cs) = (c :: (succAux cs).1, false) := by
  simp [succAux, hr]

/-! ## 繰り上がりと値 -/

/-- `0…0` に続けて読むのと、1 少ない値から `9…9` を読んで 1 足すのは同じ。 -/
theorem foldl_decimalStep_zeros_nines (n : Nat) : ∀ a : Nat,
    (List.replicate n Ascii.zero).foldl decimalStep (a + 1)
      = (List.replicate n (0x39 : Byte)).foldl decimalStep a + 1 := by
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    have e : decimalStep (a + 1) Ascii.zero = decimalStep a 0x39 + 1 := by
      have e₀ : digitValue Ascii.zero = 0 := by decide
      have e₉ : digitValue (0x39 : Byte) = 9 := by decide
      unfold decimalStep
      omega
    rw [List.replicate_succ, List.replicate_succ, List.foldl_cons, List.foldl_cons, e, ih]

/-- 最上位から繰り上がるのは、すべての桁が `9` のときで、結果の桁はすべて `0` になる。 -/
theorem succAux_carry : ∀ s : List Byte, (succAux s).2 = true →
    s = List.replicate s.length (0x39 : Byte) ∧
      (succAux s).1 = List.replicate s.length Ascii.zero
  | [], _ => ⟨rfl, rfl⟩
  | c :: cs, h => by
    by_cases hr : (succAux cs).2 = true
    · by_cases hc : c = 0x39
      · obtain ⟨h₁, h₂⟩ := succAux_carry cs hr
        subst hc
        rw [succAux_cons_carry_nine hr]
        constructor
        · show (0x39 : Byte) :: cs = (0x39 : Byte) :: List.replicate cs.length 0x39
          rw [← h₁]
        · show Ascii.zero :: (succAux cs).1 = Ascii.zero :: List.replicate cs.length Ascii.zero
          rw [h₂]
      · rw [succAux_cons_carry hr hc] at h
        simp at h
    · rw [succAux_cons_noCarry hr] at h
      simp at h

/-- 繰り上がりがなければ、どの値から読み進めても結果は 1 だけ大きい。 -/
theorem succAux_value : ∀ s : List Byte, (succAux s).2 = false → (∀ c ∈ s, IsDigit c) →
    ∀ acc : Nat, (succAux s).1.foldl decimalStep acc = s.foldl decimalStep acc + 1
  | [], h, _, _ => by simp [succAux] at h
  | c :: cs, h, hall, acc => by
    have hc : IsDigit c := hall c (by simp)
    have hcs : ∀ x ∈ cs, IsDigit x := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    by_cases hr : (succAux cs).2 = true
    · by_cases h9 : c = 0x39
      · subst h9
        rw [succAux_cons_carry_nine hr] at h
        simp at h
      · obtain ⟨h₁, h₂⟩ := succAux_carry cs hr
        have estep : decimalStep acc (c + 1) = decimalStep acc c + 1 := by
          have hs := hc.succ_digitValue
          unfold decimalStep
          omega
        rw [succAux_cons_carry hr h9]
        show ((succAux cs).1).foldl decimalStep (decimalStep acc (c + 1))
          = cs.foldl decimalStep (decimalStep acc c) + 1
        rw [h₂, estep, foldl_decimalStep_zeros_nines, ← h₁]
    · have hr' : (succAux cs).2 = false := by simpa using hr
      rw [succAux_cons_noCarry hr]
      exact succAux_value cs hr' hcs (decimalStep acc c)

theorem succAux_forall_isDigit : ∀ s : List Byte, (∀ c ∈ s, IsDigit c) →
    ∀ c ∈ (succAux s).1, IsDigit c
  | [], _ => by
    intro c hc
    cases hc
  | c :: cs, hall => by
    have hc : IsDigit c := hall c (by simp)
    have ih := succAux_forall_isDigit cs (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    by_cases hr : (succAux cs).2 = true
    · by_cases h9 : c = 0x39
      · subst h9
        rw [succAux_cons_carry_nine hr]
        show ∀ x ∈ Ascii.zero :: (succAux cs).1, IsDigit x
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl rfl
        · exact ih x hx
      · rw [succAux_cons_carry hr h9]
        show ∀ x ∈ (c + 1) :: (succAux cs).1, IsDigit x
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hc.succ_isPositiveDigit h9).isDigit
        · exact ih x hx
    · rw [succAux_cons_noCarry hr]
      show ∀ x ∈ c :: (succAux cs).1, IsDigit x
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact ih x hx

/-- 繰り上がりがなく、元の先頭が 0 でないか 1 桁なら、結果の先頭は 0 でない。 -/
theorem succAux_head {c : Byte} {cs : List Byte} (h : (succAux (c :: cs)).2 = false)
    (hc : IsDigit c) (hpos : IsPositiveDigit c ∨ cs = []) :
    ∃ d ds, (succAux (c :: cs)).1 = d :: ds ∧ IsPositiveDigit d := by
  by_cases hr : (succAux cs).2 = true
  · by_cases h9 : c = 0x39
    · subst h9
      rw [succAux_cons_carry_nine hr] at h
      simp at h
    · rw [succAux_cons_carry hr h9]
      exact ⟨c + 1, (succAux cs).1, rfl, hc.succ_isPositiveDigit h9⟩
  · rw [succAux_cons_noCarry hr]
    rcases hpos with hpos | rfl
    · exact ⟨c, (succAux cs).1, rfl, hpos⟩
    · exact absurd rfl hr

theorem numericIdentifier_cons {d : Byte} {ds : List Byte} (hd : IsPositiveDigit d)
    (hds : ∀ c ∈ ds, IsDigit c) : NumericIdentifier (d :: ds) := by
  cases ds with
  | nil => exact .positive hd
  | cons d' ds' => exact .positiveDigits hd (Digits.of_forall _ (List.cons_ne_nil _ _) hds)

/-- 数値識別子に 1 を足した結果は数値識別子で、値がちょうど 1 大きい。 -/
theorem succDigits_spec {s : List Byte} (h : NumericIdentifier s) :
    NumericIdentifier (succDigits s) ∧ decimalValue (succDigits s) = decimalValue s + 1 := by
  have hall := h.forall_isDigit
  unfold succDigits
  by_cases hcarry : (succAux s).2 = true
  · obtain ⟨h₁, h₂⟩ := succAux_carry s hcarry
    rw [ite_eq_left hcarry, h₂]
    constructor
    · exact numericIdentifier_cons (by decide) (fun c hc => by
        rw [List.eq_of_mem_replicate hc]
        exact Or.inl rfl)
    · have e : decimalStep 0 (0x31 : Byte) = 0 + 1 := by decide
      show (List.replicate s.length Ascii.zero).foldl decimalStep (decimalStep 0 0x31)
        = s.foldl decimalStep 0 + 1
      rw [e, foldl_decimalStep_zeros_nines, ← h₁]
  · have hcarry' : (succAux s).2 = false := by simpa using hcarry
    rw [ite_eq_right hcarry]
    constructor
    · cases s with
      | nil => exact absurd rfl hcarry
      | cons c cs =>
        have hpos : IsPositiveDigit c ∨ cs = [] := by
          cases h with
          | zero => exact Or.inr rfl
          | positive hd => exact Or.inl hd
          | positiveDigits hd _ => exact Or.inl hd
        obtain ⟨d, ds, hds, hd⟩ := succAux_head hcarry' (hall c (by simp)) hpos
        have hdig := succAux_forall_isDigit (c :: cs) hall
        rw [hds] at hdig ⊢
        exact numericIdentifier_cons hd (fun x hx => hdig x (List.mem_cons_of_mem _ hx))
    · exact succAux_value s hcarry' hall 0

/-! ## 構成要素の場合ごとの値 -/

theorem Spec.Components.nextPatch_of_normal {c : Components} (h : c.preRelease = []) :
    c.nextPatch = { major := c.major, minor := c.minor, patch := succDigits c.patch,
                    preRelease := [], build := [] } :=
  ite_eq_left h

theorem Spec.Components.nextPatch_of_preRelease {c : Components} (h : c.preRelease ≠ []) :
    c.nextPatch = { major := c.major, minor := c.minor, patch := c.patch,
                    preRelease := [], build := [] } :=
  ite_eq_right h

theorem Spec.Components.nextMinor_of_bump {c : Components}
    (h : c.patch ≠ [Ascii.zero] ∨ c.preRelease = []) :
    c.nextMinor = { major := c.major, minor := succDigits c.minor, patch := [Ascii.zero],
                    preRelease := [], build := [] } :=
  ite_eq_left h

theorem Spec.Components.nextMinor_of_keep {c : Components}
    (h : ¬ (c.patch ≠ [Ascii.zero] ∨ c.preRelease = [])) :
    c.nextMinor = { major := c.major, minor := c.minor, patch := [Ascii.zero],
                    preRelease := [], build := [] } :=
  ite_eq_right h

theorem Spec.Components.nextMajor_of_bump {c : Components}
    (h : c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = []) :
    c.nextMajor = { major := succDigits c.major, minor := [Ascii.zero], patch := [Ascii.zero],
                    preRelease := [], build := [] } :=
  ite_eq_left h

theorem Spec.Components.nextMajor_of_keep {c : Components}
    (h : ¬ (c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = [])) :
    c.nextMajor = { major := c.major, minor := [Ascii.zero], patch := [Ascii.zero],
                    preRelease := [], build := [] } :=
  ite_eq_right h

/-! ## 条件の対応 -/

theorem decimalValue_zero : decimalValue [Ascii.zero] = 0 := by decide

theorem decimalValue_eq_zero_iff {s : List Byte} (h : NumericIdentifier s) :
    decimalValue s = 0 ↔ s = [Ascii.zero] := by
  have h' := decimalValue_inj h NumericIdentifier.zero
  rwa [decimalValue_zero] at h'

theorem Spec.Components.toVersion_preRelease_eq_nil (c : Components) :
    c.toVersion.preRelease = [] ↔ c.preRelease = [] :=
  List.map_eq_nil_iff

/-! ## 妥当性の保存 -/

theorem Spec.Components.WF.nextPatch_wf {c : Components} (h : c.WF) : c.nextPatch.WF := by
  by_cases hpre : c.preRelease = []
  · rw [Components.nextPatch_of_normal hpre]
    exact ⟨h.major, h.minor, (succDigits_spec h.patch).1, by simp, by simp⟩
  · rw [Components.nextPatch_of_preRelease hpre]
    exact ⟨h.major, h.minor, h.patch, by simp, by simp⟩

theorem Spec.Components.WF.nextMinor_wf {c : Components} (h : c.WF) : c.nextMinor.WF := by
  by_cases hb : c.patch ≠ [Ascii.zero] ∨ c.preRelease = []
  · rw [Components.nextMinor_of_bump hb]
    exact ⟨h.major, (succDigits_spec h.minor).1, .zero, by simp, by simp⟩
  · rw [Components.nextMinor_of_keep hb]
    exact ⟨h.major, h.minor, .zero, by simp, by simp⟩

theorem Spec.Components.WF.nextMajor_wf {c : Components} (h : c.WF) : c.nextMajor.WF := by
  by_cases hb : c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = []
  · rw [Components.nextMajor_of_bump hb]
    exact ⟨(succDigits_spec h.major).1, .zero, .zero, by simp, by simp⟩
  · rw [Components.nextMajor_of_keep hb]
    exact ⟨h.major, .zero, .zero, by simp, by simp⟩

/-! ## 仕様の繰り上げとの一致 -/

/-- バイト列のままのパッチの繰り上げは、仕様の繰り上げと一致する。 -/
theorem Spec.Components.toVersion_nextPatch {c : Components} (h : c.WF) :
    c.nextPatch.toVersion = c.toVersion.nextPatch := by
  by_cases hpre : c.preRelease = []
  · rw [Components.nextPatch_of_normal hpre,
      Version.nextPatch_of_normal ((Components.toVersion_preRelease_eq_nil c).mpr hpre)]
    show Version.mk (decimalValue c.major) (decimalValue c.minor)
        (decimalValue (succDigits c.patch)) [] []
      = Version.mk (decimalValue c.major) (decimalValue c.minor) (decimalValue c.patch + 1) [] []
    rw [(succDigits_spec h.patch).2]
  · rw [Components.nextPatch_of_preRelease hpre,
      Version.nextPatch_of_preRelease
        (fun e => hpre ((Components.toVersion_preRelease_eq_nil c).mp e))] <;> rfl

/-- バイト列のままのマイナーの繰り上げは、仕様の繰り上げと一致する。 -/
theorem Spec.Components.toVersion_nextMinor {c : Components} (h : c.WF) :
    c.nextMinor.toVersion = c.toVersion.nextMinor := by
  have hcond : (c.patch ≠ [Ascii.zero] ∨ c.preRelease = []) ↔
      (c.toVersion.patch ≠ 0 ∨ c.toVersion.preRelease = []) :=
    or_congr (not_congr (decimalValue_eq_zero_iff h.patch).symm)
      (Components.toVersion_preRelease_eq_nil c).symm
  by_cases hb : c.patch ≠ [Ascii.zero] ∨ c.preRelease = []
  · rw [Components.nextMinor_of_bump hb, Version.nextMinor_of_bump (hcond.mp hb)]
    show Version.mk (decimalValue c.major) (decimalValue (succDigits c.minor))
        (decimalValue [Ascii.zero]) [] []
      = Version.mk (decimalValue c.major) (decimalValue c.minor + 1) 0 [] []
    rw [(succDigits_spec h.minor).2, decimalValue_zero]
  · rw [Components.nextMinor_of_keep hb,
      Version.nextMinor_of_keep (fun hv => hb (hcond.mpr hv))]
    show Version.mk (decimalValue c.major) (decimalValue c.minor)
        (decimalValue [Ascii.zero]) [] []
      = Version.mk (decimalValue c.major) (decimalValue c.minor) 0 [] []
    rw [decimalValue_zero]

/-- バイト列のままのメジャーの繰り上げは、仕様の繰り上げと一致する。 -/
theorem Spec.Components.toVersion_nextMajor {c : Components} (h : c.WF) :
    c.nextMajor.toVersion = c.toVersion.nextMajor := by
  have hcond : (c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = []) ↔
      (c.toVersion.minor ≠ 0 ∨ c.toVersion.patch ≠ 0 ∨ c.toVersion.preRelease = []) :=
    or_congr (not_congr (decimalValue_eq_zero_iff h.minor).symm)
      (or_congr (not_congr (decimalValue_eq_zero_iff h.patch).symm)
        (Components.toVersion_preRelease_eq_nil c).symm)
  by_cases hb : c.minor ≠ [Ascii.zero] ∨ c.patch ≠ [Ascii.zero] ∨ c.preRelease = []
  · rw [Components.nextMajor_of_bump hb, Version.nextMajor_of_bump (hcond.mp hb)]
    show Version.mk (decimalValue (succDigits c.major)) (decimalValue [Ascii.zero])
        (decimalValue [Ascii.zero]) [] []
      = Version.mk (decimalValue c.major + 1) 0 0 [] []
    rw [(succDigits_spec h.major).2, decimalValue_zero]
  · rw [Components.nextMajor_of_keep hb,
      Version.nextMajor_of_keep (fun hv => hb (hcond.mpr hv))]
    show Version.mk (decimalValue c.major) (decimalValue [Ascii.zero])
        (decimalValue [Ascii.zero]) [] []
      = Version.mk (decimalValue c.major) 0 0 [] []
    rw [decimalValue_zero]

/-! ## 構成要素の繰り上げが満たす性質 -/

/-- パッチの繰り上げの結果は、元より高い通常バージョンのうち最も低い。 -/
theorem Spec.Components.nextPatch_spec {c : Components} (h : c.WF) :
    IsLeastAbove Version.IsPatchRelease c.toVersion c.nextPatch.toVersion := by
  rw [Components.toVersion_nextPatch h]
  exact Version.nextPatch_isLeast _

/-- マイナーの繰り上げの結果は、元より高くパッチが 0 である通常バージョンのうち最も低い。 -/
theorem Spec.Components.nextMinor_spec {c : Components} (h : c.WF) :
    IsLeastAbove Version.IsMinorRelease c.toVersion c.nextMinor.toVersion := by
  rw [Components.toVersion_nextMinor h]
  exact Version.nextMinor_isLeast _

/-- メジャーの繰り上げの結果は、元より高くマイナーとパッチが 0 である通常バージョンのうち最も低い。 -/
theorem Spec.Components.nextMajor_spec {c : Components} (h : c.WF) :
    IsLeastAbove Version.IsMajorRelease c.toVersion c.nextMajor.toVersion := by
  rw [Components.toVersion_nextMajor h]
  exact Version.nextMajor_isLeast _

end SemVer
