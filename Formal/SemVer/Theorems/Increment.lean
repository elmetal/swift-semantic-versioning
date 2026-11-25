import SemVer.Spec.Increment
import SemVer.Theorems.Precedence

/-!
# 繰り上げ(§6〜§8)の性質

`nextPatch`、`nextMinor`、`nextMajor` が、それぞれの種類のリリースのうち
元より高くて最も低いものであること(`IsLeastAbove`)を示す。
この条件を満たすバージョンは優先順位について一意なので、繰り上げの結果は仕様から一通りに決まる。
-/

namespace SemVer.Spec

/-! ## 優先順位と (major, minor, patch) の関係 -/

theorem Version.Lt.triple_le {v w : Version} (h : v.Lt w) :
    v.major < w.major ∨ (v.major = w.major ∧
      (v.minor < w.minor ∨ (v.minor = w.minor ∧ v.patch ≤ w.patch))) := by
  rcases h with h | ⟨e₁, h | ⟨e₂, h | ⟨e₃, _⟩⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e₁, Or.inl h⟩
  · exact Or.inr ⟨e₁, Or.inr ⟨e₂, Nat.le_of_lt h⟩⟩
  · exact Or.inr ⟨e₁, Or.inr ⟨e₂, Nat.le_of_eq e₃⟩⟩

/-- 通常バージョンが何かより低いなら、(major, minor, patch) が真に小さい。 -/
theorem Version.Lt.triple_lt_of_normal {v w : Version} (hv : v.preRelease = []) (h : v.Lt w) :
    v.major < w.major ∨ (v.major = w.major ∧
      (v.minor < w.minor ∨ (v.minor = w.minor ∧ v.patch < w.patch))) := by
  rcases h with h | ⟨e₁, h | ⟨e₂, h | ⟨_, h⟩⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e₁, Or.inl h⟩
  · exact Or.inr ⟨e₁, Or.inr ⟨e₂, h⟩⟩
  · rw [hv] at h
    exact False.elim h

theorem Version.Lt.of_triple_lt {v w : Version}
    (h : v.major < w.major ∨ (v.major = w.major ∧
      (v.minor < w.minor ∨ (v.minor = w.minor ∧ v.patch < w.patch)))) : v.Lt w := by
  rcases h with h | ⟨e₁, h | ⟨e₂, h⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e₁, Or.inl h⟩
  · exact Or.inr ⟨e₁, Or.inr ⟨e₂, Or.inl h⟩⟩

/-- §11.3: プレリリース版は、対応する通常バージョンより低い。 -/
theorem Version.Lt.of_preRelease {v w : Version}
    (e₁ : v.major = w.major) (e₂ : v.minor = w.minor) (e₃ : v.patch = w.patch)
    (hv : v.preRelease ≠ []) (hw : w.preRelease = []) : v.Lt w := by
  refine Or.inr ⟨e₁, Or.inr ⟨e₂, Or.inr ⟨e₃, ?_⟩⟩⟩
  rw [hw]
  cases hpre : v.preRelease with
  | nil => exact absurd hpre hv
  | cons a as => exact True.intro

/-! ## 場合ごとの値 -/

theorem Version.nextPatch_of_normal {v : Version} (h : v.preRelease = []) :
    v.nextPatch = { major := v.major, minor := v.minor, patch := v.patch + 1 } :=
  ite_eq_left h

theorem Version.nextPatch_of_preRelease {v : Version} (h : v.preRelease ≠ []) :
    v.nextPatch = { major := v.major, minor := v.minor, patch := v.patch } :=
  ite_eq_right h

theorem Version.nextMinor_of_bump {v : Version} (h : v.patch ≠ 0 ∨ v.preRelease = []) :
    v.nextMinor = { major := v.major, minor := v.minor + 1, patch := 0 } :=
  ite_eq_left h

theorem Version.nextMinor_of_keep {v : Version} (h : ¬ (v.patch ≠ 0 ∨ v.preRelease = [])) :
    v.nextMinor = { major := v.major, minor := v.minor, patch := 0 } :=
  ite_eq_right h

theorem Version.nextMajor_of_bump {v : Version}
    (h : v.minor ≠ 0 ∨ v.patch ≠ 0 ∨ v.preRelease = []) :
    v.nextMajor = { major := v.major + 1, minor := 0, patch := 0 } :=
  ite_eq_left h

theorem Version.nextMajor_of_keep {v : Version}
    (h : ¬ (v.minor ≠ 0 ∨ v.patch ≠ 0 ∨ v.preRelease = [])) :
    v.nextMajor = { major := v.major, minor := 0, patch := 0 } :=
  ite_eq_right h

/-! ## 通常バージョンに対しては §6〜§8 の単純な繰り上げと一致する -/

/-- §6: 通常バージョンのパッチの繰り上げは、パッチを 1 上げる。 -/
theorem Version.nextPatch_of_isNormal {v : Version} (h : v.IsNormal) :
    v.nextPatch = { major := v.major, minor := v.minor, patch := v.patch + 1 } :=
  Version.nextPatch_of_normal h

/-- §7: 通常バージョンのマイナーの繰り上げは、マイナーを 1 上げてパッチを 0 に戻す。 -/
theorem Version.nextMinor_of_isNormal {v : Version} (h : v.IsNormal) :
    v.nextMinor = { major := v.major, minor := v.minor + 1, patch := 0 } :=
  Version.nextMinor_of_bump (Or.inr h)

/-- §8: 通常バージョンのメジャーの繰り上げは、メジャーを 1 上げてマイナーとパッチを 0 に戻す。 -/
theorem Version.nextMajor_of_isNormal {v : Version} (h : v.IsNormal) :
    v.nextMajor = { major := v.major + 1, minor := 0, patch := 0 } :=
  Version.nextMajor_of_bump (Or.inr (Or.inr h))

/-! ## 最小性 -/

/-- パッチの繰り上げは、元より高い通常バージョンのうち最も低い。 -/
theorem Version.nextPatch_isLeast (v : Version) :
    IsLeastAbove Version.IsPatchRelease v v.nextPatch := by
  unfold IsLeastAbove
  by_cases h : v.preRelease = []
  · rw [Version.nextPatch_of_normal h]
    refine ⟨rfl, Version.Lt.of_triple_lt (Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.lt_add_one _⟩⟩), ?_⟩
    intro u hu hvu huw
    have h₁ := Version.Lt.triple_lt_of_normal h hvu
    have h₂ : u.major < v.major ∨ (u.major = v.major ∧
        (u.minor < v.minor ∨ (u.minor = v.minor ∧ u.patch < v.patch + 1))) :=
      Version.Lt.triple_lt_of_normal hu huw
    omega
  · rw [Version.nextPatch_of_preRelease h]
    refine ⟨rfl, Version.Lt.of_preRelease rfl rfl rfl h rfl, ?_⟩
    intro u hu hvu huw
    have h₁ := Version.Lt.triple_le hvu
    have h₂ : u.major < v.major ∨ (u.major = v.major ∧
        (u.minor < v.minor ∨ (u.minor = v.minor ∧ u.patch < v.patch))) :=
      Version.Lt.triple_lt_of_normal
        (w := { major := v.major, minor := v.minor, patch := v.patch }) hu huw
    omega

/-- マイナーの繰り上げは、元より高くパッチが 0 である通常バージョンのうち最も低い。 -/
theorem Version.nextMinor_isLeast (v : Version) :
    IsLeastAbove Version.IsMinorRelease v v.nextMinor := by
  unfold IsLeastAbove
  by_cases h : v.patch ≠ 0 ∨ v.preRelease = []
  · rw [Version.nextMinor_of_bump h]
    refine ⟨And.intro rfl rfl,
      Version.Lt.of_triple_lt (Or.inr ⟨rfl, Or.inl (Nat.lt_add_one _)⟩), ?_⟩
    intro u hu hvu huw
    obtain ⟨huNormal, huPatch⟩ := hu
    have h₂ : u.major < v.major ∨ (u.major = v.major ∧
        (u.minor < v.minor + 1 ∨ (u.minor = v.minor + 1 ∧ u.patch < 0))) :=
      Version.Lt.triple_lt_of_normal huNormal huw
    rcases h with hp | hpre
    · have h₁ := Version.Lt.triple_le hvu
      omega
    · have h₁ := Version.Lt.triple_lt_of_normal hpre hvu
      omega
  · have hp : v.patch = 0 := Decidable.byContradiction fun hne => h (Or.inl hne)
    have hpre : v.preRelease ≠ [] := fun e => h (Or.inr e)
    rw [Version.nextMinor_of_keep h]
    refine ⟨And.intro rfl rfl, Version.Lt.of_preRelease rfl rfl hp hpre rfl, ?_⟩
    intro u hu hvu huw
    obtain ⟨huNormal, _⟩ := hu
    have h₁ := Version.Lt.triple_le hvu
    have h₂ : u.major < v.major ∨ (u.major = v.major ∧
        (u.minor < v.minor ∨ (u.minor = v.minor ∧ u.patch < 0))) :=
      Version.Lt.triple_lt_of_normal huNormal huw
    omega

/-- メジャーの繰り上げは、元より高くマイナーとパッチが 0 である通常バージョンのうち最も低い。 -/
theorem Version.nextMajor_isLeast (v : Version) :
    IsLeastAbove Version.IsMajorRelease v v.nextMajor := by
  unfold IsLeastAbove
  by_cases h : v.minor ≠ 0 ∨ v.patch ≠ 0 ∨ v.preRelease = []
  · rw [Version.nextMajor_of_bump h]
    refine ⟨And.intro rfl (And.intro rfl rfl),
      Version.Lt.of_triple_lt (Or.inl (Nat.lt_add_one _)), ?_⟩
    intro u hu hvu huw
    obtain ⟨huNormal, huMinor, huPatch⟩ := hu
    have h₂ : u.major < v.major + 1 ∨ (u.major = v.major + 1 ∧
        (u.minor < 0 ∨ (u.minor = 0 ∧ u.patch < 0))) :=
      Version.Lt.triple_lt_of_normal huNormal huw
    rcases h with hm | hp | hpre
    · have h₁ := Version.Lt.triple_le hvu
      omega
    · have h₁ := Version.Lt.triple_le hvu
      omega
    · have h₁ := Version.Lt.triple_lt_of_normal hpre hvu
      omega
  · have hm : v.minor = 0 := Decidable.byContradiction fun hne => h (Or.inl hne)
    have hp : v.patch = 0 := Decidable.byContradiction fun hne => h (Or.inr (Or.inl hne))
    have hpre : v.preRelease ≠ [] := fun e => h (Or.inr (Or.inr e))
    rw [Version.nextMajor_of_keep h]
    refine ⟨And.intro rfl (And.intro rfl rfl), Version.Lt.of_preRelease rfl hm hp hpre rfl, ?_⟩
    intro u hu hvu huw
    obtain ⟨huNormal, _, _⟩ := hu
    have h₁ := Version.Lt.triple_le hvu
    have h₂ : u.major < v.major ∨ (u.major = v.major ∧
        (u.minor < 0 ∨ (u.minor = 0 ∧ u.patch < 0))) :=
      Version.Lt.triple_lt_of_normal huNormal huw
    omega

/-- 「元より高くて最も低い」バージョンは、優先順位について一意。 -/
theorem IsLeastAbove.unique {P : Version → Prop} {v w w' : Version}
    (h : IsLeastAbove P v w) (h' : IsLeastAbove P v w') : w.PrecedenceEq w' := by
  obtain ⟨hP, hlt, hleast⟩ := h
  obtain ⟨hP', hlt', hleast'⟩ := h'
  rcases Version.Lt.trichotomous w w' with hlt'' | heq | hgt
  · exact absurd hlt'' (hleast' w hP hlt)
  · exact heq
  · exact absurd hgt (hleast w' hP' hlt')

/-! ## 帰結 -/

/-- §7: マイナーを上げるとパッチは 0 に戻る。 -/
theorem Version.nextMinor_patch (v : Version) : v.nextMinor.patch = 0 :=
  (Version.nextMinor_isLeast v).1.2

/-- §8: メジャーを上げるとマイナーとパッチは 0 に戻る。 -/
theorem Version.nextMajor_minor_patch (v : Version) :
    v.nextMajor.minor = 0 ∧ v.nextMajor.patch = 0 :=
  (Version.nextMajor_isLeast v).1.2

theorem Version.lt_nextPatch (v : Version) : v.Lt v.nextPatch :=
  (Version.nextPatch_isLeast v).2.1

theorem Version.lt_nextMinor (v : Version) : v.Lt v.nextMinor :=
  (Version.nextMinor_isLeast v).2.1

theorem Version.lt_nextMajor (v : Version) : v.Lt v.nextMajor :=
  (Version.nextMajor_isLeast v).2.1

/-- 繰り上げの結果は通常バージョン。 -/
theorem Version.nextPatch_isNormal (v : Version) : v.nextPatch.IsNormal :=
  (Version.nextPatch_isLeast v).1

theorem Version.nextMinor_isNormal (v : Version) : v.nextMinor.IsNormal :=
  (Version.nextMinor_isLeast v).1.1

theorem Version.nextMajor_isNormal (v : Version) : v.nextMajor.IsNormal :=
  (Version.nextMajor_isLeast v).1.1

end SemVer.Spec
