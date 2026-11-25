import SemVer.Parser.Correctness
import SemVer.Theorems.Denotation

/-!
# 文字列と抽象的なバージョンの対応

参照パーサと構成要素の意味を合成し、バージョン文字列と `Spec.Version` を直接対応させる。

主定理:

* `parseVersion_sound`: 成功したら、結果は妥当で、文字列に戻すと入力と一致する。
* `parseVersion_complete`: 妥当なバージョンを文字列にして読むと、元のバージョンが得られる。
* `validSemVer_iff_parseVersion`: BNF で妥当であることと、`parseVersion` が成功することは同値。

したがって、BNF で妥当な文字列と妥当な `Version` は 1 対 1 に対応する。
-/

namespace SemVer

open Spec

/-- バージョン文字列を読む。BNF で妥当でなければ `none`。 -/
def parseVersion (s : List Byte) : Option Version :=
  (parse s).map Components.toVersion

/-- バージョンを文字列にする。 -/
def Spec.Version.render (v : Version) : List Byte :=
  v.toComponents.render

/-- 成功したら、結果は妥当で、文字列に戻すと入力と一致する。 -/
theorem parseVersion_sound {s : List Byte} {v : Version} (h : parseVersion s = some v) :
    v.WF ∧ v.render = s := by
  unfold parseVersion at h
  cases hp : parse s with
  | none =>
    rw [hp] at h
    cases h
  | some c =>
    rw [hp] at h
    obtain rfl : c.toVersion = v := Option.some.inj h
    obtain ⟨hwf, hrender⟩ := parse_sound hp
    refine ⟨hwf.toVersion_wf, ?_⟩
    show c.toVersion.toComponents.render = s
    rw [hwf.toComponents_toVersion, hrender]

/-- 妥当なバージョンを文字列にして読むと、元のバージョンが得られる。 -/
theorem parseVersion_complete {v : Version} (h : v.WF) : parseVersion v.render = some v := by
  show (parse v.toComponents.render).map Components.toVersion = some v
  rw [parse_complete h.toComponents_wf]
  show some v.toComponents.toVersion = some v
  rw [h.toVersion_toComponents]

/-- BNF で妥当であることと、`parseVersion` が成功することは同値。 -/
theorem validSemVer_iff_parseVersion (s : List Byte) :
    ValidSemVer s ↔ ∃ v, parseVersion s = some v := by
  rw [validSemVer_iff_parse]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.toVersion, by unfold parseVersion; rw [hc]; rfl⟩
  · rintro ⟨v, hv⟩
    unfold parseVersion at hv
    cases hp : parse s with
    | none =>
      rw [hp] at hv
      cases hv
    | some c => exact ⟨c, rfl⟩

/-- BNF で妥当な文字列とは、妥当なバージョンを文字列にしたものである。 -/
theorem validSemVer_iff_version (s : List Byte) :
    ValidSemVer s ↔ ∃ v : Version, v.WF ∧ v.render = s := by
  rw [validSemVer_iff_parseVersion]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, parseVersion_sound hv⟩
  · rintro ⟨v, hwf, rfl⟩
    exact ⟨v, parseVersion_complete hwf⟩

/-- 妥当なバージョンは、文字列が同じなら等しい。 -/
theorem Spec.Version.render_injective {v₁ v₂ : Version} (h₁ : v₁.WF) (h₂ : v₂.WF)
    (h : v₁.render = v₂.render) : v₁ = v₂ :=
  Option.some.inj ((parseVersion_complete h₁).symm.trans (h ▸ parseVersion_complete h₂))

/-- 同じ文字列が 2 つの異なるバージョンとして読まれることはない。 -/
theorem parseVersion_injective {s₁ s₂ : List Byte} {v : Version}
    (h₁ : parseVersion s₁ = some v) (h₂ : parseVersion s₂ = some v) : s₁ = s₂ :=
  (parseVersion_sound h₁).2.symm.trans (parseVersion_sound h₂).2

end SemVer
