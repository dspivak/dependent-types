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

Awodey, later with Newstead, showed how polynomial pseudomonads $(u,\1,\Sigma)$ with extra structure (termed "natural models" by Awodey) hold within them the categorical semantics for dependent type theory. Their work presented these ideas clearly but ultimately led them outside of the category of polynomial functors in order to explain all of the structure possessed by such models of type theory.

This paper builds off that work---explicating the categorical semantics of dependent type theory by axiomatizing them \emph{entirely} in the language of polynomial functors. In order to handle the higher-categorical coherences required for such an explanation, we work with polynomial functors internally in the language of Homotopy Type Theory, which allows for higher-dimensional structures such as pseudomonads, etc. to be expressed purely in terms of the structure of a suitably-chosen $\infty$-category of polynomial functors. The move from set theory to Homotopy Type Theory thus has a twofold effect of enabling a simpler exposition of natural models, which is at the same time amenable to formalization in a proof assistant, such as Agda.

Moreover, the choice to remain firmly within the setting of polynomial functors reveals many additional structures of natural models that were otherwise left implicit or not considered by Awodey \& Newstead. Chief among these, we highlight the fact that every polynomial pseudomonad $(u,\1,\Sigma)$ as above that is also equipped with structure to interpret dependent product types gives rise to a self-distributive law $u\tri u\to u\tri u$, which witnesses the usual distributive law of dependent products over dependent sums.

\end{abstract}

# Introduction

The central idea of dependent type theory (c.f. \cite{martin-lof1975intuitionistic}) is that \emph{order of events} is fundamental to the mathematical story arc: when playing out any specific example story within that arc, the beginning of the story affects not only the later events, but even the very terms with which the later events will be described. For example, in the story arc of conditional probability, one may say ``now if the set $P$ that we are asked to condition on happens to have measure zero, we must stop; but assuming that's not the case then the result will be a new probability measure.'' Here the story teller is saying that no terms will describe what happens if $P$ has measure zero, whereas otherwise the terms of standard probability will apply.

Dependent types form a logical system with syntax, rules of computation, and robust categorical semantics. In \cite{awodey2014natural,awodey2018polynomial}, Awodey and later Newstead show that there is a strong connection between dependent type theory and polynomial functors, via their concept of *natural models*, which cleanly solve the problem of *strictififying* certain identities that typically hold only up to isomorphism in arbitrary categories, but must hold *strictly* in order for these to soundly model dependent type theory. The solution to this problem offered by Awodey and Newstead makes use of the type-theoretic concept of a *universe*. Such universes then turn out to naturally be regarded as polynomial functors on a suitably-chosen category of presheaves, satisfying a certain *representability* condition.

Although the elementary structure of natural models is thus straightforwardly described by considering them as objects in a category of polynomial functors, Awodey and Newstead were ultimately led outside of this category in order to fully explicate those parts of natural models that require identities to hold only *up to isomorphism*, rather than strictly. There is thus an evident tension between *strict* and *weak* identities that has not yet been fully resolved in the story of natural models. In the present work, we build on Awodey and Newstead's work to fully resolve this impasse by showing how type universes can be fully axiomatized in terms of polynomial functors, by working with polynomial functors internally in the language of *Homotopy Type Theory* (HoTT). We thus come full circle from Awodey's original motivation to develop natural models *of* Homotopy Type Theory, to describing natural models *in* Homotopy Type Theory.

The ability for us to tell the story of natural models as set entirely in the category of polynomial functors has a great simplifying effect upon the resultant theory, and reveals many additional structures, both of polynomial universes, and of the category of polynomial functors as a whole. As an illustration of this, we show how every polynomial universe $u$, regarded as a polynomial pseudomonad with additional structure, gives rise to self-distributive law $u\tri u\to u\tri u$, which in particular witnesses the usual distributive law of dependent products over dependent sums.

Moreover, the move from set theory to HoTT as a setting in which to tell this story enables new tools to be applied for its telling. In particular, the account of polynomial universes we develop is well-suited to formalization in a proof assistant, and we present such a formalization in Agda. This paper is thus itself a literate Agda document in which all results have been fully formalized and checked for validity.

```agda
{-# OPTIONS --without-K --rewriting #-}
module part1v2 where
```

The structure of this paper is as follows:

* In Section 2, we give an introductory presentation of dependent type theory and natural models, followed by a recap the basics of HoTT that will be used throughout the rest of the paper.
* In Section 3, we outline the basic theory of polynomial functors in HoTT, culminating in a demonstration of how to model dependent pair types using polynomial functors. In order to show that these polynomial functors are in fact monads, however, we will need some additional technology, to which we devote the following section.
* In Section 4, we introduce the key concept of a *polynomial universe* as a polynomial functor satisfying a certain *univalence* condition, that allows us to straightforwardly derive the monad laws for polynomial universes equipped with the structure to interpret dependent pair types.
* In Section 5, building on the ideas of the previous sections, we show how to model dependent function types with polynomial functors, and demonstrate that any polynomial universe equipped with this structure -- along with the aforementioned structure for interpreting dependent pair types -- gives rise to a self-distributive law of the corresponding monad.
* In Section 6, we conclude the paper by sketching how this theory may be further developed to handle identity types, inductive types, and other key concepts from dependent type theory.