# Caml* for VS Code

Syntax highlighting for the **Caml\*** language — a simplified, stratified,
dependently-typed clone of F\* (source files use the `.cst` extension).

## Features

- TextMate grammar covering the full surface syntax:
  - Keywords: `module let rec and in val assume type match with fun if then else
    when forall exists requires ensures assert Lemma`
  - Qualifiers: `private irreducible unfold noeq logic`
  - Primitive types (`int bool float unit string`), type variables (`'a`),
    data constructors and module paths (`Cons`, `Demo.List`)
  - Refinement/logic operators (`-> <: ==> <==> /\ \/ ~ == <> <= >= = < > : | .`),
    arithmetic (`+ - * / %`)
  - Numeric (int/float) and string literals with escapes
  - Pragmas (`#set-options #push-options #pop-options #check #eval`) and
    attributes (`[@@ ... ]`)
  - Nested block comments `(* ... *)` and line comments `// ...`
- Language configuration: comment toggling, bracket matching, auto-closing pairs.

## Install (local development)

VS Code loads any extension placed in its extensions folder:

```sh
# from this directory
cp -r . ~/.vscode/extensions/camlstar-0.1.0
```

Then reload VS Code (`Developer: Reload Window`). Open any `.cst` file and the
language will show as **Caml\*** in the status bar.

Alternatively, to iterate on the grammar: open this folder in VS Code and press
`F5` to launch an Extension Development Host, or run
`Developer: Inspect Editor Tokens and Scopes` on a `.cst` file to see the scope
assigned to any token.

## Packaging (optional)

With [`vsce`](https://github.com/microsoft/vscode-vsce) installed:

```sh
vsce package        # produces camlstar-0.1.0.vsix
code --install-extension camlstar-0.1.0.vsix
```

## Scope

This extension currently provides **syntax highlighting only** (a TextMate
grammar). Language-server features — diagnostics from the Caml\* type checker,
go-to-definition, hover types — are out of scope for now.
