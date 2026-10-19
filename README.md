# ProjectTemplate

A template for Lean 4 projects that depend on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Prerequisites

Install Lean via [elan](https://github.com/leanprover/elan) (see the
[Lean installation guide](https://lean-lang.org/install/)). The correct Lean version is
picked up automatically from `lean-toolchain`.

## 1. Rename the project

After creating your repository from this template, rename it from `ProjectTemplate` to your
own project name:

```bash
./customize.sh MyProject
```

This updates `lakefile.toml`, `lake-manifest.json`, the Lean imports and this README's title, and
renames `ProjectTemplate.lean` and `ProjectTemplate/` to `MyProject.lean` and `MyProject/`.
The name must be a valid Lean module name (letters, digits and underscores, starting with a
letter; UpperCamelCase is conventional). Commit the result, then delete `customize.sh`.

## 2. Get the Mathlib cache

Compiling Mathlib from source takes hours, so download the prebuilt files instead:

```bash
lake exe cache get
```

Re-run this whenever you change the Mathlib version (or if your editor starts rebuilding
Mathlib files).

## 3. Build and work on the project

```bash
lake build
```

- Put your Lean files under `MyProject/` and import each one from `MyProject.lean`, so that
  `lake build` (and CI) checks them.
- Open the repository folder (not a single file) in VS Code with the Lean 4 extension.

## Updating Mathlib

Change the `rev` under `[[require]]` in `lakefile.toml` to the new Mathlib tag, and set
`lean-toolchain` to match. Then run:

```bash
lake update mathlib
lake exe cache get
lake build
```

Alternatively, run the **Update Dependencies** workflow from the GitHub *Actions* tab: it
opens a pull request if the update builds, or an issue if it doesn't. (Uncomment the
`schedule` block in `.github/workflows/update.yml` to run it automatically.)

## GitHub setup

- **CI**: every push and pull request is built by `.github/workflows/lean_action_ci.yml`.
- To let the update workflow open pull requests, go to **Settings → Actions → General** and
  tick **Allow GitHub Actions to create and approve pull requests**.
- To publish docs to GitHub Pages, set **Settings → Pages → Source** to "GitHub Actions" and
  uncomment the `docgen-action` line in `lean_action_ci.yml`.
