/// [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) のバージョン。
///
/// 仕様の BNF で妥当な文字列からだけ作れる。数値部分に桁数の上限はない。
///
/// ```swift
/// let a = SemanticVersion("1.0.0-rc.1")!
/// let b = SemanticVersion("1.0.0")!
/// a < b  // true
/// ```
///
/// 比較と等価性は仕様 §11 の優先順位に従う。ビルドメタデータは優先順位に影響しないので、
/// `1.0.0+a` と `1.0.0+b` は `==` で等しい。文字列として同じかどうかは `description` で比べる。
public struct SemanticVersion: Sendable {
    /// 不変条件: `components.isWellFormed`。イニシャライザが `Parser.parse` の結果だけを入れる。
    let components: Components

    /// UTF-8 のバイト列からバージョンを作る。仕様の BNF で妥当でなければ `nil`。
    public init?(utf8 bytes: some Sequence<UInt8>) {
        guard let components = Parser.parse(Array(bytes)[...]) else {
            return nil
        }
        self.components = components
    }
}

// MARK: - 文字列との変換

extension SemanticVersion: LosslessStringConvertible {
    /// 文字列からバージョンを作る。仕様の BNF で妥当でなければ `nil`。
    public init?(_ description: String) {
        self.init(utf8: description.utf8)
    }

    /// バージョン文字列。作るときに渡した文字列と一致する。
    public var description: String {
        String(decoding: Parser.render(components), as: UTF8.self)
    }
}

// MARK: - 構成要素

extension SemanticVersion {
    /// メジャーバージョンの 10 進表記。桁数に上限がないので文字列で返す。
    public var major: String {
        String(decoding: components.major, as: UTF8.self)
    }

    /// マイナーバージョンの 10 進表記。
    public var minor: String {
        String(decoding: components.minor, as: UTF8.self)
    }

    /// パッチバージョンの 10 進表記。
    public var patch: String {
        String(decoding: components.patch, as: UTF8.self)
    }

    /// プレリリース識別子。プレリリース版でなければ空。
    public var prereleaseIdentifiers: [String] {
        components.preRelease.map { String(decoding: $0, as: UTF8.self) }
    }

    /// ビルドメタデータの識別子。なければ空。
    public var buildMetadataIdentifiers: [String] {
        components.build.map { String(decoding: $0, as: UTF8.self) }
    }

    /// プレリリース版かどうか。
    public var isPrerelease: Bool {
        !components.preRelease.isEmpty
    }
}

// MARK: - 優先順位

extension SemanticVersion: Comparable {
    /// 優先順位が等しい。ビルドメタデータは無視する。
    public static func == (lhs: SemanticVersion, rhs: SemanticVersion) -> Bool {
        Precedence.precedenceEqual(lhs.components, rhs.components)
    }

    /// 左辺の優先順位が右辺より低い。
    public static func < (lhs: SemanticVersion, rhs: SemanticVersion) -> Bool {
        Precedence.less(lhs.components, rhs.components)
    }
}

extension SemanticVersion: Hashable {
    /// `==` と整合するよう、ビルドメタデータはハッシュに含めない。
    public func hash(into hasher: inout Hasher) {
        hasher.combine(components.major)
        hasher.combine(components.minor)
        hasher.combine(components.patch)
        hasher.combine(components.preRelease)
    }
}
