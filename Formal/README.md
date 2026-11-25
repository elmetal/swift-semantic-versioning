# Formal — Semantic Versioning 2.0.0 の形式仕様と証明

[Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html)(CC BY 3.0)を Lean 4 で形式化し、
Swift 実装が満たすべき性質を入力空間全体について証明する。

## ビルド

```bash
lake build
```

警告はすべてエラー扱いなので、`sorry` が残っているとビルドは失敗する。
依存パッケージはなく、Lean のバージョンは `lean-toolchain` で固定している。

Swift 側のテストが使うベクタは、次のコマンドで生成し直す。`Vectors.lean` や定義を変えたら実行し、差分をコミットする。

```bash
lake exe vectors ../Tests/SemanticVersioningTests/Vectors
```

## 構成

| パス | 役割 | 信頼の扱い |
| --- | --- | --- |
| `SemVer/Spec/Grammar.lean` | BNF の直訳 | 信頼の基点(人が仕様書と照合する) |
| `SemVer/Spec/Precedence.lean` | 抽象的なバージョンと §11 の優先順位 | 信頼の基点 |
| `SemVer/Spec/Components.lean` | 文字列の構成要素(識別子はバイト列のまま) | 信頼の基点 |
| `SemVer/Spec/Denotation.lean` | 構成要素が表すバージョン(10 進数の解釈) | 信頼の基点 |
| `SemVer/Spec/Increment.lean` | §6〜§8 の繰り上げ(「元より高い、その種類のリリースのうち最も低いもの」) | 信頼の基点 |
| `SemVer/Spec/Decidable.lean` | 例を評価するための判定インスタンス | 仕様の意味を変えない |
| `SemVer/Theorems/` | 仕様から導かれる定理 | Lean が検査する |
| `SemVer/Parser/` | 参照パーサと、BNF との同値性の証明 | Lean が検査する |
| `SemVer/Model/` | バイト列のままの比較と繰り上げ(Swift 実装の写し)と、仕様との一致の証明 | Lean が検査する |
| `SemVer/Examples.lean`, `SemVer/*/Examples.lean` | 具体例による点検 | テスト(証明ではない) |
| `SemVer/Audit.lean` | 定理が依存する公理の固定 | Lean が検査する |
| `Vectors.lean` | Swift との差分テスト用ベクタの生成 | 証明済みの定義を実行するだけ |

## 3 つの表現とその対応

```
バージョン文字列 (List Byte)
    │  parse / render          … BNF と同値であることを証明済み
構成要素 Components            … 識別子はバイト列のまま。桁数に上限なし
    │  toVersion / toComponents … 妥当なもの同士で互いに逆であることを証明済み
抽象的なバージョン Version      … 数値は Nat。§11 の優先順位はここで定義
```

Swift 実装の値は `Components` に対応させる。数値識別子を整数型に変換しないので、オーバーフローが起きない。
比較も `Components` の上で直接行い(`Components.Lt`)、`toVersion` を通した §11 の優先順位と一致することを証明している。

## 条項と形式化の対応

| 条項 | 内容 | 定義 | 定理・検査 |
| --- | --- | --- | --- |
| BNF | 妥当なバージョン文字列 | `ValidSemVer` ほか `Grammar.lean` の全定義 | `validSemVer_iff_parse`, `validSemVer_iff_components`, `validSemVer_iff_version` |
| §2 | X.Y.Z は先頭ゼロのない非負整数 | `NumericIdentifier`, `decimalValue` | `numericIdentifier_iff`, `decimalValue_decimalDigits`, `NumericIdentifier.decimalDigits_decimalValue` |
| §6〜§8 | 繰り上げと下位桁のリセット | `Version.nextPatch` / `nextMinor` / `nextMajor`, `IsLeastAbove` | `nextPatch_isLeast`, `nextMinor_isLeast`, `nextMajor_isLeast`, `IsLeastAbove.unique`, `nextPatch_of_isNormal` ほか |
| §9 | プレリリース | `PreRelease`, `PreReleaseIdentifier`, `PreReleaseId.ofBytes` | `preReleaseIdentifier_iff`, `alphanumericIdentifier_iff`, `PreReleaseIdentifier.toBytes_ofBytes` |
| §10 | ビルドメタデータ | `Build`, `BuildIdentifier` | `buildIdentifier_iff`, `Version.Lt.build_irrelevant`, `Version.PrecedenceEq.of_build` |
| §11.1〜§11.2 | major, minor, patch の順に数値比較 | `Version.Lt` | `Version.Lt.irrefl` / `trans` / `asymm` / `trichotomous` |
| §11.3 | プレリリース版は通常版より低い | `PreReleaseLt` | `PreReleaseLt.cons_nil` |
| §11.4.1〜§11.4.3 | 識別子 1 個の比較 | `PreReleaseId.Lt`, `AsciiLt`, `LexLt` | `PreReleaseId.Lt.strictTotalOrder` |
| §11.4.4 | 識別子が多い方が高い | `PreReleaseLt`, `LexLt` | `PreReleaseLt.append_right` |
| §11 全体 | 優先順位は全順序 | `Version.Lt`, `Version.PrecedenceEq` | `Version.Lt.trichotomous`, `Version.PrecedenceEq.not_lt`, `Version.Lt.congr_left` / `congr_right`, `Version.precedenceEq_iff` |

§1、§3〜§5 は公開 API の宣言やリリース運用についての規則で、ライブラリの振る舞いではないため対象外。

## 主な定理

文法と構文解析(`SemVer/Parser/`):

- `validSemVer_iff_parse`: BNF で妥当であることと、参照パーサが成功することは同値。
- `parse_sound`: 成功したら、結果は妥当で、文字列に戻すと入力と一致する。
- `parse_complete`: 妥当な構成要素を文字列にして読むと、元の構成要素が得られる。
- `Components.render_injective`: 妥当な文字列の分解は一意(文法に曖昧さがない)。
- `parseVersion_sound`, `parseVersion_complete`, `validSemVer_iff_version`: 上と同じことが抽象的な `Version` についても成り立つ。
  BNF で妥当な文字列と妥当な `Version` は 1 対 1 に対応する。

優先順位(`SemVer/Theorems/Precedence.lean`):

- `Version.Lt.trichotomous`、`Version.PrecedenceEq.not_lt`、`Version.Lt.asymm` を合わせると、
  任意の 2 つのバージョンについて「低い」「優先順位が等しい」「高い」のちょうど 1 つが成り立つ。
  Swift の `Comparable` と `Equatable` をこの同値(ビルドメタデータを無視)で定義すれば、プロトコルの要求を満たす。

実装モデル(`SemVer/Model/`):

- `numericLt_iff`: 数値識別子を「桁数が少ない方が小さく、同じ桁数なら辞書順」で比べた結果は、数値の大小と一致する。
- `Components.lt_iff`, `Components.precedenceEq_iff`: 妥当な構成要素について、バイト列のままの比較は §11 の優先順位と一致する。
- `Components.lt_trichotomous`, `lt_irrefl`, `lt_trans`, `lt_asymm`, `not_lt_of_precedenceEq`:
  したがって構成要素の比較も、優先順位の等しさを法とする全順序である。

繰り上げ(`SemVer/Theorems/Increment.lean`, `SemVer/Model/IncrementCorrectness.lean`):

仕様 §6〜§8 は、通常バージョンから次のリリースを出すときの規則しか定めておらず、プレリリース版の繰り上げには定めがない。
このライブラリは繰り上げを §11 の順序だけで定める。結果は node-semver の `inc` と同じになる。

| 操作 | 定義 | `1.2.3` | `1.2.3-rc.1` | `1.2.0-rc.1` |
| --- | --- | --- | --- | --- |
| `nextPatch` | 元より高い通常バージョンのうち最も低いもの | `1.2.4` | `1.2.3` | `1.2.0` |
| `nextMinor` | 元より高く、パッチが 0 の通常バージョンのうち最も低いもの | `1.3.0` | `1.3.0` | `1.2.0` |
| `nextMajor` | 元より高く、マイナーとパッチが 0 の通常バージョンのうち最も低いもの | `2.0.0` | `2.0.0` | `2.0.0` |

- `nextPatch_isLeast`, `nextMinor_isLeast`, `nextMajor_isLeast`: 各関数が上の定義を満たす。
- `IsLeastAbove.unique`: 定義を満たすバージョンは優先順位について一意。つまり結果は定義から一通りに決まる。
- `nextPatch_of_isNormal` ほか: 通常バージョンに対しては、§6〜§8 の「1 上げて下位を 0 に戻す」と一致する。
- `succDigits_spec`: 数字列のまま 1 を足した結果は、数値識別子のまま値がちょうど 1 大きい。
- `Components.toVersion_nextPatch` ほか: バイト列のままの繰り上げは、仕様の繰り上げと一致する。

## Swift 実装との対応

Swift のコード(`Sources/SemanticVersioning/`)は、下の Lean 定義を関数単位で写して書いてある。
Lean の再帰は Swift ではループになっている箇所があるが、分岐の構造は同じにしている。

| Swift | Lean | 仕様との関係を示す定理 |
| --- | --- | --- |
| `Grammar.isPositiveDigit` ほか文字クラス | `IsPositiveDigit`, `IsDigit`, `IsLetter`, `IsNonDigit`, `IsIdentifierCharacter` | 定義そのもの |
| `Grammar.isDigits` | `digits_iff` の右辺 | `digits_iff` |
| `Grammar.isNumericIdentifier` | `numericIdentifier_iff` の右辺 | `numericIdentifier_iff` |
| `Grammar.isAlphanumericIdentifier` | `alphanumericIdentifier_iff` の右辺 | `alphanumericIdentifier_iff` |
| `Grammar.isPreReleaseIdentifier`, `isBuildIdentifier` | `preReleaseIdentifier_iff`, `buildIdentifier_iff` の右辺 | 同左 |
| `Components`, `Components.isWellFormed` | `Components`, `Components.WF` | 定義そのもの |
| `Parser.splitFirst`, `splitOn` | `splitFirst`, `splitOn` | `splitFirst_reassemble`, `join_splitOn` ほか |
| `Parser.parseIdentifiers`, `assemble`, `decompose`, `parse` | 同名 | `validSemVer_iff_parse`, `parse_sound`, `parse_complete` |
| `Parser.joinIdentifiers`, `suffix`, `render` | `joinIdentifiers`, `suffix`, `Components.render` | `parse_sound`, `parse_complete` |
| `Precedence.lexLess`, `asciiLess` | `LexLt`, `AsciiLt` | `LexLt.strictTotalOrder` |
| `Precedence.numericLess` | `NumericLt` | `numericLt_iff` |
| `Precedence.identifierLess`, `preReleaseLess` | `IdentifierLt`, `PreReleaseBytesLt` | `identifierLt_iff`, `preReleaseBytesLt_iff` |
| `Precedence.less`, `precedenceEqual` | `Components.Lt`, `Components.PrecedenceEq` | `Components.lt_iff`, `Components.precedenceEq_iff` |
| `SemanticVersion` の `<`, `==` | 上の 2 つ | `Components.lt_trichotomous` ほか |
| `Digits.decimal` | `decimalDigits` | `numericIdentifier_decimalDigits`, `decimalValue_decimalDigits` |
| `Digits.successor` | `succDigits` | `succDigits_spec` |
| `Increment.nextPatch`, `nextMinor`, `nextMajor` | `Components.nextPatch`, `nextMinor`, `nextMajor` | `Components.toVersion_nextPatch` ほか, `Components.WF.nextPatch_wf` ほか |
| `SemanticVersion.init(major:minor:patch:)` | `Version.toComponents` | `Version.WF.toComponents_wf`, `Version.WF.toVersion_toComponents` |
| `SemanticVersion.isIdentical(to:)` | 構成要素の等しさ | `Components.eq_iff_render_eq` |

この対応そのものは機械的に証明されていない。Swift のコードと Lean の定義が同じであることは、次の 2 つで支えている。

- 関数ごとに 1 対 1 で照合できる小ささに保つ(Swift 側の中身は 4 ファイル、コメント込みで 393 行)。
- `Vectors.lean` が Lean の定義を実行して出力したベクタと、Swift の結果を突き合わせる
  (`Tests/SemanticVersioningTests/VectorTests.swift`)。
  - 文字クラス: 256 個のバイトすべて。
  - 文法: 実装が区別するバイトの種類ごとの代表 7 文字で、7 文字以下の文字列すべて(960,800 件)と、
    妥当な接頭辞の後ろに 4〜5 文字を続けた文字列すべて(28,011 件)。
  - 優先順位: 見本約 1,400 個のすべての組。
  - 繰り上げ: 見本約 1,400 個それぞれの、パッチ・マイナー・メジャーの繰り上げ結果。
  - 10 進表記: `UInt` の上限までの境界値。

Swift のコンパイラと標準ライブラリ(`Array`、`UInt8` の比較など)は信頼する。

## 公理

優先順位の定理は公理に依存しない(`precedenceEq_iff` だけ `propext`)。
文法、構文解析、実装モデルの定理は Lean の標準の公理(`propext`、`Classical.choice`、`Quot.sound`)に依存する。
どちらも `SemVer/Audit.lean` で固定している。

## 未着手

- Swift のループと Lean の再帰の対応を、Lean 側にループの形の関数を置いて証明すること。
- DFA の遷移表の生成と、それが `ValidSemVer` と同じ言語を受理することの証明。
