# Contributing

Contributions to the shared algebraic-geometry library, source-faithful
projects, flagship challenges, blueprints, and mathematical reviews are
welcome.

## Repository roles

- `MainProjects/` contains flagship formalizations organized by mathematical
  dependency.
- `FormalizedSources/` contains developments that follow particular books,
  papers, or online references.
- FormalizedSources/StacksProject follows the eight imported official Stacks
  parts; each PartXX directory is one project and one blueprint, with numbered
  descriptive chapter files such as blueprint/src/ch01-introduction.tex and
  blueprint/src/ch02-conventions.tex.
- `shared/` contains reusable declarations independent of one source.

Keep each pull request focused on one project or one coherent infrastructure
change. Add a route to `config.yaml`. Mark it `planned: true` only while it has
no blueprint or Lean sources.

## hgraph workflow

The workspace website is generated from the root manifest:

```bash
hgraph sync --manifest config.yaml
hgraph site --manifest config.yaml --out _site/index.html
hgraph serve --manifest config.yaml
```

Planned routes are skipped by synchronization until their project-local
`hgraph/config.yaml`, blueprint, and optional Lean sources exist. The GitHub
Pages workflow installs a pinned hgraph revision, validates the manifest, and
publishes `_site/` on every push to `main`.

## Stacks Project blueprints

Stacks chapters are imported from
[stacks-project](https://github.com/stacks/stacks-project) with
`FormalizedSources/StacksProject/convert_stacks_chapter.py`. Policy:

- keep mathematical wording **source-faithful** (do not lightly paraphrase);
- adapt presentation for hgraph (prefixed labels, titles, `\source{stacks:TAG}`);
- retain GFDL notices; see the `blueprint/src/PROVENANCE.md` in each Part.

Regenerate a chapter only when intentionally refreshing from upstream.

## Mathematical provenance

Source-faithful developments should identify the reference and preserve its
mathematical organization. Blueprint statements should use stable labels and
record dependencies with `\uses{...}`. Add `\lean{...}` only for corresponding
Lean declarations, and add `\leanok` only after the declaration has been
checked.

## License

By contributing, you agree that your original contributions are licensed under
the repository's [Apache 2.0 License](LICENSE). Stacks Project text remains
under the GFDL 1.2+. Other third-party source material remains subject to its
original license.
