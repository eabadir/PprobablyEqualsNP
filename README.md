# PprobablyEqualsNP

This repository contains a formalization (in Lean 4) and a LaTeX paper for the claim that physics is NP-complete and that \(P = NP\), based significantly on the all but lost math proof I call Rota's Entropy Theorem, from my former MIT professor, the late Gian-Carlo Rota. His book on Probability Theory, never published, has this and many other gems:https://archive.org/details/GianCarlo_Rota_and_Kenneth_Baclawski__An_Introduction_to_Probability_and_Random_Processes/page/n367/mode/2up

The title of the paper is a play on the famous "P vs NP" problem in computer science and the notion from information theory/Shannon's Coding Theorem that in the limit, the error of coding a message becomes arbitrarily small as the message length increases - P equals NP in the limit. The paper is a work in progress, and I welcome feedback and contributions.


## Getting Started

### 1. Install Lean and VS Code Extensions

- **Lean 4**:  
  - Visit [leanprover-community.github.io/get_started.html](https://leanprover-community.github.io/get_started.html) for installation instructions.
  - Recommended: Use the [elan toolchain manager](https://leanprover-community.github.io/get_started.html#installing-lean-and-mathlib).
- **VS Code Extensions**:  
  - Install [Visual Studio Code](https://code.visualstudio.com/).
  - In VS Code, install the **Lean 4 extension** (search for "lean4" in the Extensions panel).
  - For LaTeX editing and PDF preview, install the **LaTeX Workshop** extension.

### 2. Build and Read the Paper

- The main paper is in `Paper/PprobablyEqualsNP_formal.tex`.
- Compile it with your favorite LaTeX tool or via VS Code's LaTeX Workshop extension.
- The compiled PDF provides the full argument and background.

### 3. Explore and Run the Lean Code

- The Lean formalization is in `PPNP/Sketches/PprobablyEqualsNP.lean`.
- Open this file in VS Code with the Lean 4 extension enabled.
- You can step through the code, check proofs, and experiment with modifications.

### 4. Feedback and Contributions

- **Feedback is very welcome!**  
  - This is my first experience coding in Lean, so suggestions on code style, libraries, or Lean best practices are appreciated.
  - More importantly, I am interested in substantive feedback on the mathematics, logic, and overall argument.
  - Critiques, questions, and alternative perspectives are encouraged.

- **Open an issue or pull request** if you have suggestions, corrections, or improvements.

---

Thank you for checking out this project!