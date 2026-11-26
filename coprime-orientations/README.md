# Coprime Orientations of Graphs

> **Paper:** *Coprime Orientations of Graphs: Structural Characterizations, Number-Theoretic Obstructions, and Complexity Dichotomy*

## Overview

An orientation $D$ of a finite simple undirected graph $G = (V, E)$ is a **coprime orientation** if
$$\gcd\bigl(\deg_D^+(v),\, \deg_D^-(v)\bigr) = 1 \qquad \text{for every } v \in V.$$
Equivalently, $\deg_D^+(v) \in \mathcal{A}(\deg_G(v)) := \{k \in \{0,\dots,\deg_G(v)\} : \gcd(k, \deg_G(v)) = 1\}$ at every vertex.

### Main Results
1. **Universal Families:** Every graph with degrees in $\{2\} \cup (2\mathbb{Z}_{\ge 0} + 1)$, every tree on $n \ge 2$ vertices, every regular bipartite graph (including all hypercubes $Q_d$, $d \ge 1$), and every complete bipartite graph $K_{a,b}$ ($a,b \ge 1$) is coprimely orientable.
2. **Power-of-2 Characterization:** A connected graph whose degrees are all powers of $2$ (with $\delta(G) \ge 2$) is coprimely orientable if and only if $|E(G)| \equiv |V(G)| \pmod{2}$; if it has a leaf, it is always coprimely orientable.
3. **Complete Graph Classification:** $K_n$ ($n \ge 1$) is coprimely orientable if and only if $n \not\equiv 1 \pmod{4}$ and $n \neq 7$.
4. **Mod-4 Uniqueness & Cut Obstruction at $d = 6$:** Among all even $d \ge 4$, $d = 6$ is the unique degree with $\gcd\{x - y : x, y \in \mathcal{A}(d)\} = 4$ (for all other even $d \ge 4$, the gcd is $2$). Consequently, no $6$-regular graph with an odd vertex subset of cut size $0$ or $2$ is coprimely orientable, yielding a $2$-edge-connected $6$-regular non-orientable graph $G_{14}$ on $14$ vertices.
5. **Prime-Power Gap Dichotomy & Sharp Complexity:** $\mathcal{A}(d)$ has no two consecutive missing integers in $[1, d-1]$ iff $d = 1$ or $d = p^k$. Thus deciding coprime orientability is in **P** whenever all degrees are $1$ or prime powers (in particular, $\Delta(G) \le 5$), and **NP-complete** for simple bipartite graphs with $\Delta(G) = 6$ (all degrees in $\{2, 3, 6\}$).

## Directory Structure

```
coprime-orientations/
├── paper/
│   ├── main.tex              # Publication-quality LaTeX manuscript (with TikZ figures)
│   └── main.pdf              # Compiled PDF (11 pages)
├── lean/
│   ├── lean-toolchain        # leanprover/lean4:v4.36.0
│   ├── lakefile.toml         # Standalone Lake config (zero external dependencies)
│   └── CoprimeOrientations.lean  # Machine-checked Lean 4 proofs (zero sorrys)
├── scripts/
│   └── verify_all.py         # Independent Python verification suite
└── README.md
```

## Verification

### Lean 4 Formal Verification
```bash
cd coprime-orientations/lean
lake build
```
Zero external dependencies (pure Lean 4 core), zero `sorry`s, zero custom axioms.

### Python Verification
```bash
python3 coprime-orientations/scripts/verify_all.py
```

### LaTeX Compilation
```bash
cd coprime-orientations/paper
pdflatex main.tex && pdflatex main.tex
```
