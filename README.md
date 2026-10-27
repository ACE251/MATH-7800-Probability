# MATH-7800-Probability
Auburn University | Fall 2026
Ph.D. in Mathematics

Overview

This repository contains my work for MATH 7800: Probability I at Auburn University, including Lean 4 formal proofs, mathematical exercises, and related course projects.

The primary goal is to develop a rigorous understanding of probability theory and measure-theoretic foundations while learning how to formalize mathematical arguments using the Lean 4 theorem prover and the Mathlib library.

Course Information

Course: MATH 7800 — Probability I

Institution: Auburn University

Semester: Fall 2026

Instructor: Dr. Le Chen

Textbook: Patrick Billingsley, Probability and Measure, 3rd Edition

Tools: Lean 4, Mathlib, Lake, VS Code, LaTeX

Topics Covered

The course explores the mathematical foundations of probability, including:

Probability spaces and probability measures

Fields and σ-fields of sets

π-systems and λ-systems

The π–λ theorem

Monotone classes and the monotone class theorem

Outer measures and measure extensions

Countable additivity and continuity of probability measures

Limit superior and limit inferior of events

Lean 4 Formalization Projects

Project A: The π–λ Theorem

Formalization of fundamental properties of λ-systems and π-systems, including closure properties and the relationship between generated λ-systems and σ-fields.

Project B: The Monotone Class Theorem

Formalization of monotone classes, fields of sets, and the conditions under which monotone classes generate σ-fields.

Learning Objectives

This repository documents my progress toward:

Writing mathematically rigorous proofs in Lean 4.

Understanding the correspondence between informal proofs and formal verification.

Developing familiarity with Lean tactics, theorem statements, and proof construction.

Applying formal methods to foundational results in probability theory.

Development Environment

Language: Lean 4

Library: Mathlib

Build system: Lake

Editor: Visual Studio Code

To build the project locally:

lake exe cache get
lake build

The project-specific Lean and dependency versions are specified in lean-toolchain and lake-manifest.json.

Reference

Billingsley, P. (1995). Probability and Measure (3rd ed.). Wiley.
