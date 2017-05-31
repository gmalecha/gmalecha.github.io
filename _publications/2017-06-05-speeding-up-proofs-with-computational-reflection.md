---
layout: publication
category: publication
title: Speeding Up Proofs with Computational Reflection
authors: Gregory Malecha
where: SF Types, Theorems, and Programming Languages
tags:
- coq
- verification
- automation
- reflection
links:
 - meetup link: https://www.meetup.com/SF-Types-Theorems-and-Programming-Languages/events/240275659/
---
One of the biggest complaints about proof assistants such as Coq is performance. Large proofs can be slow to both construct and to check which reduces the "interactive" nature of interactive proof assistants and makes maintenance painful. However, while the richness of dependent type theory is partially to blame for this slowness, it also allows us to use computational reflection to extend the proof checker to build and check proofs quickly. In computational reflection, we convert proof objects in to computations and run them on Coq's bytecode virtual machine to achieve orders of magnitude improvements in proof construction and checking. In this talk I walk through how computational reflection works using a few small examples. Time permitting, I will discuss how these ideas can be used to build larger scale reflective automation (the MirrorCore project) including an Ltac-like DSL for reflective automation that provides some of the speed benefits of computational reflection without some of the drawbacks.