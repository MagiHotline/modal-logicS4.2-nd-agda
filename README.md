# Deductive System for Modal Logic S4.2 in Agda

## Project Description
This project was developed as part of a university internship and aims at the **implementation, in the proof assistant [Agda](https://agda.readthedocs.io/)**, of a **deductive system in natural deduction for modal logic S4.2**.

The work lies within the fields of **mathematical logic** and **theoretical computer science**, adopting a formal approach to the representation and verification of logical systems through **dependent types**.

The project follows the **deep embedding** methodology — that is, representing one logical system within another (Agda) using **inductive types** — with the goal of studying its **metatheory** and proving key properties such as **normalization**.

---

## Theoretical Context
Modal logic **S4.2** is an extension of **S4** that adds specific axioms to model notions of **necessity** and **possibility** in richer contexts, such as epistemic or topological frameworks.

Within the **natural deduction** formalism, inference rules are expressed in terms of the introduction and elimination of logical connectives. In this project, these rules will be **encoded in Agda** using **inductive types**.

---

## Requirements
- **Agda** ≥ 2.6.4  
  → [Official installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
- **Agda Standard Library** (recommended)
  ```bash
  agda --version
  agda -i . -i /path/to/stdlib
