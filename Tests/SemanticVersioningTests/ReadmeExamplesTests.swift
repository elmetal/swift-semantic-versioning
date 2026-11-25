import SemanticVersioning
import Testing

/// README.md と README.ja.md に載せているコード例が、書いてあるとおりに動くことを確かめる。
/// README の例を変えたら、ここも合わせて変える。公開 API だけを使う。
@Suite("README のコード例")
struct ReadmeExamplesTests {
    @Test("解析")
    func parsing() throws {
        let version = try #require(SemanticVersion("1.2.3-rc.1+build.5"))

        #expect(version.major == "1")
        #expect(version.minor == "2")
        #expect(version.patch == "3")
        #expect(version.prereleaseIdentifiers == ["rc", "1"])
        #expect(version.buildMetadataIdentifiers == ["build", "5"])
        #expect(version.isPrerelease)
        #expect(version.description == "1.2.3-rc.1+build.5")

        #expect(SemanticVersion("1.2") == nil)
        #expect(SemanticVersion("v1.2.3") == nil)
        #expect(SemanticVersion("01.2.3") == nil)
        #expect(SemanticVersion("1.2.3-01") == nil)
        #expect(SemanticVersion("1.2.3+01") != nil)
        #expect(SemanticVersion(" 1.2.3") == nil)

        #expect(UInt(version.major) == Optional(1))
        #expect(SemanticVersion(utf8: Array("1.2.3".utf8))?.description == "1.2.3")
    }

    @Test("数値から作る")
    func fromNumbers() {
        #expect(SemanticVersion(major: 1, minor: 2, patch: 3).description == "1.2.3")
    }

    @Test("比較")
    func comparing() throws {
        let versions = ["1.0.0", "1.0.0-rc.1", "1.0.0-alpha", "1.0.0-beta.11", "1.0.0-beta.2"]
            .compactMap { SemanticVersion($0) }
        #expect(versions.count == 5)
        #expect(
            versions.sorted().map(\.description)
                == ["1.0.0-alpha", "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"])

        let a = try #require(SemanticVersion("1.0.0+linux"))
        let b = try #require(SemanticVersion("1.0.0+macos"))
        #expect(a == b)
        #expect(!a.isIdentical(to: b))
        #expect(Set([a, b]).count == 1)
    }

    @Test("繰り上げの表", arguments: [
        ("1.2.3", "1.2.4", "1.3.0", "2.0.0"),
        ("1.2.3-rc.1", "1.2.3", "1.3.0", "2.0.0"),
        ("1.2.0-rc.1", "1.2.0", "1.2.0", "2.0.0"),
    ])
    func incrementTable(_ string: String, _ patch: String, _ minor: String, _ major: String) throws {
        let version = try #require(SemanticVersion(string))
        #expect(version.nextPatch.description == patch)
        #expect(version.nextMinor.description == minor)
        #expect(version.nextMajor.description == major)
    }

    @Test("繰り上げ")
    func incrementing() throws {
        #expect(try #require(SemanticVersion("1.2.3")).nextMinor.description == "1.3.0")
        #expect(try #require(SemanticVersion("1.2.0-rc.1")).nextMinor.description == "1.2.0")

        let huge = try #require(SemanticVersion("18446744073709551615.0.0"))
        #expect(huge.description == "\(UInt64.max).0.0")
        #expect(huge.nextMajor.description == "18446744073709551616.0.0")
    }
}
