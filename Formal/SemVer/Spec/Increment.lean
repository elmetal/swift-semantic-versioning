import SemVer.Spec.Precedence

/-!
# Semantic Versioning 2.0.0 — バージョンの繰り上げ(§6〜§8)

出典: <https://semver.org/spec/v2.0.0.html>(CC BY 3.0)

仕様が定めるのは「上げた桁より下位を 0 に戻す」ことだけである。
プレリリースとビルドメタデータを落とすのはこのライブラリの設計上の選択で、仕様の要求ではない
(未確定。API 設計時に見直す)。
-/

namespace SemVer.Spec

/-- §6: パッチバージョンを上げる。 -/
def Version.nextPatch (v : Version) : Version :=
  { major := v.major, minor := v.minor, patch := v.patch + 1 }

/-- §7: マイナーバージョンを上げ、パッチを 0 に戻す。 -/
def Version.nextMinor (v : Version) : Version :=
  { major := v.major, minor := v.minor + 1, patch := 0 }

/-- §8: メジャーバージョンを上げ、マイナーとパッチを 0 に戻す。 -/
def Version.nextMajor (v : Version) : Version :=
  { major := v.major + 1, minor := 0, patch := 0 }

end SemVer.Spec
