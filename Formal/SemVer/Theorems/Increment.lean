import SemVer.Spec.Increment
import SemVer.Theorems.Precedence

/-!
# 繰り上げ(§6〜§8)の性質

繰り上げたバージョンは元より必ず高く、パッチ、マイナー、メジャーの順に高くなる。
-/

namespace SemVer.Spec

/-- §7: マイナーを上げるとパッチは 0 に戻る。 -/
theorem Version.nextMinor_patch (v : Version) : v.nextMinor.patch = 0 := rfl

/-- §8: メジャーを上げるとマイナーとパッチは 0 に戻る。 -/
theorem Version.nextMajor_minor_patch (v : Version) :
    v.nextMajor.minor = 0 ∧ v.nextMajor.patch = 0 := ⟨rfl, rfl⟩

theorem Version.lt_nextPatch (v : Version) : v.Lt v.nextPatch :=
  .inr ⟨rfl, .inr ⟨rfl, .inl (Nat.lt_add_one v.patch)⟩⟩

theorem Version.nextPatch_lt_nextMinor (v : Version) : v.nextPatch.Lt v.nextMinor :=
  .inr ⟨rfl, .inl (Nat.lt_add_one v.minor)⟩

theorem Version.nextMinor_lt_nextMajor (v : Version) : v.nextMinor.Lt v.nextMajor :=
  .inl (Nat.lt_add_one v.major)

theorem Version.lt_nextMinor (v : Version) : v.Lt v.nextMinor :=
  (v.lt_nextPatch).trans v.nextPatch_lt_nextMinor

theorem Version.lt_nextMajor (v : Version) : v.Lt v.nextMajor :=
  (v.lt_nextMinor).trans v.nextMinor_lt_nextMajor

end SemVer.Spec
