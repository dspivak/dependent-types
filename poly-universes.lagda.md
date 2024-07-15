---
title: Polynomial Universes and Dependent Types
author:
    - C.B. Aberlé
    - David I. Spivak
documentclass: memoir
classoption:
    - 11pt
    - oneside
    - article
---

\begin{abstract}
Awodey, later with Newstead, showed how polynomial monads $(u,\1,\Sigma)$ with extra structure hold within them the syntax and rules for dependent type theory. Their work presented these ideas cleanly but within a complex setting: using pseudomonads and pseudo-algebras in a tricategory.

This paper builds off that work---explicating the syntax and rules for dependent type theory by axiomatizing them in the language of polynomial functors---but from a different starting point. First we work in a more basic setting, that of a 1-category with two monoidal products. Second, rather than considering pseudo-algebras of any sort, we define a seemingly new categorical structure that houses the axioms for dependent type theory in a polynomial setting. This structure picks up something that Awodey-Newstead seem to have missed: the distributive law for products over sums. Indeed, one result of our axiomatization is that any universe monad will always carry a self-distributive law $u\tri u\to u\tri u$.
\end{abstract}

# Introduction

Dependent type theory \cite{martin-lof1975intuitionistic} was founded by Per Martin-Löf in 1975 to formalize constructive mathematics. The basic idea is that \emph{order of events} is fundamental to a mathematical story arc: when playing out any specific example story in that arc, the beginning of the story affects not only the later events, but even the very terms with which the later events will be described. For example, in the story arc of conditional probability, one may say ``now if the set $P$ that we are asked to condition on happens to have measure zero, we must stop; but assuming that's not the case then the result will be a new probability measure.'' Here the story teller is saying that no terms will describe what happens if $P$ has measure zero, whereas otherwise the terms of standard probability will apply.

Dependent types form a logical system with syntax, conversion rules, and methods of deduction. In \cite{awodey2014natural,awodey2018polynomial}, Awodey and later Newstead show that there is a strong connection between dependent type theory and polynomial functors. The present work follows from this remarkable discovery, but differs in two key respects:

```agda
module poly-universes where

open import Agda.Builtin.Equality
```

# Background on HoTT and Polynomial Functors

## Homotopy Type Theory

## Polynomials in HoTT

### Basics

### Univalence

### The Vertical-Cartesian Factorization System

### The Composition and Dirichlet Monoidal Products

### The $\upuparrows$ and $(-)^=$ Functors

# Polynomial Universes \& Jump Monads

## Polynomial Universes

## Jump Monads \& Distributive Laws