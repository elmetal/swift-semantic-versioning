import SemVer.Spec.Grammar

/-!
# バージョン文字列の構成要素

バージョン文字列を区切り記号で分けた結果。識別子はバイト列のまま持つので、
数値識別子の桁数に上限はない。Swift 実装の値の表現もこの形に対応させる。

文字列との対応(`render` と `parse`)は `SemVer.Parser` で定義し、BNF と一致することを証明する。
-/

namespace SemVer.Spec

/-- バージョン文字列の構成要素。各識別子はバイト列のまま持つ。 -/
structure Components where
  major : List Byte
  minor : List Byte
  patch : List Byte
  /-- プレリリース識別子の列。空なら `-` 以降がない。 -/
  preRelease : List (List Byte)
  /-- ビルド識別子の列。空なら `+` 以降がない。 -/
  build : List (List Byte)
  deriving DecidableEq, Repr

/-- 構成要素が文法上妥当である。 -/
structure Components.WF (c : Components) : Prop where
  major : NumericIdentifier c.major
  minor : NumericIdentifier c.minor
  patch : NumericIdentifier c.patch
  preRelease : ∀ i ∈ c.preRelease, PreReleaseIdentifier i
  build : ∀ i ∈ c.build, BuildIdentifier i

end SemVer.Spec
