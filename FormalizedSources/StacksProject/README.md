# Stacks Project

Source-faithful hgraph blueprints for the mathematical chapters of the
[Stacks Project](https://stacks.math.columbia.edu/), organized by its
official Parts 1-8. Part 9 (Miscellany) is omitted.

## Layout

The workspace has exactly eight Stacks projects: one project and one
self-contained blueprint per official Part.

~~~text
Part01_Preliminaries/
  blueprint/src/
    content.tex
    macros.tex
    refs.bib
    stacks-my.bib
    PROVENANCE.md
    GFDL-1.2.txt
    ch01-introduction.tex
    ch02-conventions.tex
    ...
  hgraph/config.yaml
...
Part08_TopicsInModuliTheory/
  blueprint/src/ch01-moduli-stacks.tex
  blueprint/src/ch02-moduli-of-curves.tex
~~~

Each Part aggregate includes its descriptive chapter files in official order.
The files are source units inside the Part blueprint, not child projects, and
there are no shared blueprint dependencies outside that Part.

The manifest registers the eight routes in the Stacks group. Together they
contain 109 Stacks chapters and about 16,172 parsed mathematical statements.

Statements carrying an upstream Stacks tag keep the structured
`\\source{stacks:TAG}` metadata and also render a clickable link to
`https://stacks.math.columbia.edu/tag/TAG`. The converter emits a standard
LaTeX `\\href` for this link because hgraph renders `\\href` in prose, whereas
project-local custom text macros are not expanded there.

The converter also rewrites the upstream Xy-pic `\\xymatrix` diagrams into
KaTeX-compatible `array` diagrams, preserving nodes, directions, and labels.
Curved paths and spacing directives are flattened because KaTeX has no Xy-pic
layout engine. Chapter-level `\\bibliography{my}` and
`\\bibliographystyle{amsalpha}` commands are omitted; each Part's local `.bib`
files remain available to hgraph's bibliography view.

## Provenance and license

Stacks text is **GFDL 1.2+** (no invariant sections). Each Part carries its own
PROVENANCE.md and GFDL-1.2.txt beside the blueprint source.

## Regenerating a chapter

The converter writes one descriptive chapter file into the selected Part.
Its --project argument is the file stem, for example
ch01-constructions-of-schemes. It does not create a new project. After
regeneration, keep the matching chapter and input entry in that Part's
blueprint/src/content.tex.

~~~bash
python3 FormalizedSources/StacksProject/convert_stacks_chapter.py \
  --src /path/to/stacks-project/schemes.tex \
  --stem schemes --title Schemes \
  --part Part02_Schemes --project ch01-schemes \
  --out-root FormalizedSources/StacksProject \
  --tags /path/to/stacks-project/tags/tags
~~~
