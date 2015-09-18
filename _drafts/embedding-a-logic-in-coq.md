---
layout: blog
category: blog
title: Embedding a Logic in Coq
---
Embedding a Logic in Coq
========================

Coq comes with a powerful, built-in logic (Gallina) with features such as inductive and dependent types, recursion, etc.
However, most uses of Coq don't study its theory, but rather use it as a logic to reason about something else.
A few examples come to mind due to my experience with program verification:

* The Verified Software Toolchain embeds a program logic for reasoning about C programs.
* Ynot embeds a logic for reasoning about imperative programs.
* Iris, ...,  all embed different logics for reasoning about concurrent program.
* Bedrock embeds a logic for reasoning about low-level imperative programs.

May of these systems are structured in a similar way, they build their logic on top of Gallina in a /shallow/ way.
While shallow encodings are not good for everything, they often allow you to get to the heart of your problem very quickly so that you can think about the problems that you would like to solve.