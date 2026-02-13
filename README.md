# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome collaboration from researchers, students, and practitioners.

## Current Coverage

- Books
  - **Author(s):** Terence Tao
  - **Full title:** *Analysis II*
  - **Publisher:** (TODO: publisher)
  - **Year:** 2022
  - **Edition / series / ISBN:** (TODO: edition/series/ISBN)
  - **Contributors:** (TODO: list contributors who formalized this book)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap01/section01/) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Books.Analysis2_Tao_2022#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Books/Analysis2_Tao_2022)
  - **Author(s):** R. Tyrrell Rockafellar
  - **Full title:** *Convex Analysis*
  - **Publisher:** (TODO: publisher)
  - **Year:** 1970
  - **Edition / series / ISBN:** (TODO: edition/series/ISBN)
  - **Contributors:** (TODO: list contributors who formalized this book)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap01/section01/) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Books.ConvexAnalysis_Rockafellar_1970#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970)
  - **Author(s):** Jiri Lebl
  - **Full title:** *Introduction to Real Analysis, Volume I*
  - **Publisher:** (TODO: publisher)
  - **Year:** 2025
  - **Edition / series / ISBN:** (TODO: edition/series/ISBN)
  - **Contributors:** (TODO: list contributors who formalized this book)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap00/section03/) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025)
  - **Author(s):** Michele Conforti, Gerard Cornuejols, Giacomo Zambelli
  - **Full title:** *Integer Programming*
  - **Publisher:** (TODO: publisher)
  - **Year:** 2014
  - **Edition / series / ISBN:** (TODO: edition/series/ISBN)
  - **Contributors:** (TODO: list contributors who formalized this book)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/) (TODO: add book pages) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Books.IntegerProgramming_Conforti_2014#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Books/IntegerProgramming_Conforti_2014)

- Papers
  - **Author(s):** Yurii Nesterov
  - **Full title:** *Smooth Minimization of Nonsmooth Functions*
  - **Publisher:** (TODO: journal/conference/publisher)
  - **Year:** 2004
  - **Series / DOI:** (TODO: series/DOI)
  - **Contributors:** (TODO: list contributors who formalized this paper)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/papers/smoothminimization_nesterov_2004/paper/) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Papers.SmoothMinimization_Nesterov_2004#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Papers/SmoothMinimization_Nesterov_2004)
  - **Author(s):** Mansour Maassaran
  - **Full title:** *On Some Local Rings*
  - **Publisher:** (TODO: journal/conference/publisher)
  - **Year:** 2025
  - **Series / DOI:** (TODO: series/DOI)
  - **Contributors:** (TODO: list contributors who formalized this paper)
  - **Links:** [Verso](https://optsuite.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/paper/) | [API docs](https://optsuite.github.io/ReasBook/docs/find?pattern=Papers.OnSomeLocalRings_Maassaran_2025#doc) | [Lean source](https://github.com/optsuite/ReasBook/tree/main/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025)

## Repository Layout

The repository is organized into a Lean source tree and a web-documentation tree:

```text
ReasBook/
├── ReasBook/                         # Main Lean project (books + papers + doc-gen target)
│   ├── Books/
│   ├── Papers/
│   ├── ReasBook.lean
│   ├── LiterateExtract.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── ReasBookWeb/                      # Verso website project
│   ├── ReasBookSite/
│   ├── static_files/
│   ├── scripts/gen_sections.py
│   ├── ReasBookSite.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── .github/workflows/deploy_pages.yml
├── build.sh
├── build-web.sh
├── serve.py
└── scripts/cleanup-generated.sh
```

## Naming Convention

Top-level content directories use:

`<Title>_<AuthorLastName>_<Year>`

Examples:

- `ConvexAnalysis_Rockafellar_1970`
- `SmoothMinimization_Nesterov_2004`
- `OnSomeLocalRings_Maassaran_2025`

## Build

From the repository root:

```bash
./build.sh
```

Build the Verso site (including API docs copied to `_site/docs`):

```bash
./build-web.sh
```

Serve the generated site locally:

```bash
python3 serve.py
```

If generated artifacts were previously committed, untrack them (without deleting local files):

```bash
./scripts/cleanup-generated.sh
```

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Sino-Russian Mathematics Center
- Great Bay University
- National Natural Science Foundation of China

## Publications

### Formalization of Optimization

- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automated Theorem Proving

- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*.
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*.

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*.

## Team

We are a group of scholars and students interested in mathematical formalization.

### Core Members

- Chenyi Li, School of Mathematical Sciences, Peking University, China (`lichenyi@stu.pku.edu.cn`)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, China (`wlma@pku.edu.cn`)
- Zichen Wang, School of Mathematical Sciences, Peking University, China (`zichenwang25@stu.pku.edu.cn`)
- Ziyu Wang, School of Mathematical Sciences, Peking University, China (`wangziyu-edu@stu.pku.edu.cn`)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, China (`wenzw@pku.edu.cn`)

### Contributors

- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwan Wu, Mingyue Xu, Yunfei Zhang, Changyun Zou

## License

Copyright (c) 2026 Chenyi Li, Wanli Ma, Zichen Wang, Ziyu Wang, Zaiwen Wen.

Released under the Apache 2.0 license. See `LICENSE` for details.
