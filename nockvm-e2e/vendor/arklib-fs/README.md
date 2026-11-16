# arklib-fs

Ten ArkLib modules (the single-salt Fiat-Shamir framework and the stopped / randomized state-restoration security
results) by Quang Dao, from upstream ArkLib pull requests #1280 (head 3444c2f7) and #1282 (head 89433a85), which were
closed on GitHub without being merged. They are vendored here unchanged except for one thing: their module names are moved from `ArkLib.*` to `ArkLibFs.*`
(the files live under `ArkLibFs/`, and the `import` lines among the ten say `ArkLibFs.`), because Lake resolves every
`ArkLib.*` module name to the ArkLib package itself. Declaration names, namespaces and proofs are unchanged; each file keeps its
own Apache-2.0 header and carries a two-line modification notice right after it (Apache-2.0, section 4(b));
`LICENSE` is ArkLib's. They build on ArkLib main c488a3a4dabd74c543ee39836523b116dbc7ba2b, which this package requires.
