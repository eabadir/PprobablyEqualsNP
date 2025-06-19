# Prompt Objectives
- Explain how one establishes equivalence between number classes in Lean code (Nat, Int, etc.). Essentially what is the "recipe"?
- Explain the notion of "decidability" in Lean and how it applies here.
- Using the physical interpretation of Review the equivalence proofs for Int and Real and lay out a plan that tries to accomplish Rat in a similarly manner straightforward manner.

# Background
Below is a project I'm working on. Next step is filling out the Rationals but, before moving on, I'd like to ground the Rationals in physical intuition. Discuss possible physical interpretations/intuition on the Rationals from a combinatoric point of view (e.g. ordered paths vs. canonical paths , etc..)

Electronic Graph Paper Theory (EGPT): This document outlines a detailed plan for a "unified" constructive framework of number theory, computational complexity, and physics within a verifiable type theoretic framework (in Lean 4). This "Phase 1" lays out a contextualized and detailed implementation plan using of a single instance of unification (the "special case") as precursor to generalized unification in Phase 2 which is not fully outlined in this document.

## Preface: EGPT

Our objective is to use these new computerized proof tools to tackle hard questions but, unfortunately, we immediately hit a roadblock. Since the physical path of a particle is "absolutely impossible to explain" it means we can't put it in an Algorithm and, therefore, the two concepts of physics computation and computer computation could never fully connect. One might argue that the inability to further analyse physics in terms of computation has lead to foundational road-blocks and the holy-grail questions like does P=NP in mathematics and a theory of quantum gravity in physics. Progress has effectively stopped for at least 50 years on the very biggest questions. This fundamental disconnect was actually discussed by the two entropy "founders" Von Neumann (quantum mechanic's version of entropy) and Shannon (computer science's version of entropy). They knew they were similar or connected in some way, but as Von Neumann reputedly said, "no one knows what Entropy is." Some 30 or 40 years later, unbeknownst to the world, MIT professor Gian-Carlo Rota, rigorously derived a mathematical equivalence between physics entropies and information theory entropy (Shannon Entropy) and made a class out of it, MIT 18.313, which he taught using an unpublished manuscript. Rota's 400 page manuscript, now translated into Lean verified proofs, are the rigorous formulation that all entropy is just one thing, and that it is computable. This connection between probability, information, entropy, and coding theory, rigorously showed that many fundamental probability distributions in physics (Bose-Einstein, Maxwell-Boltzmann, Fermi-Dirac) arise from entropy considerations and can be understood through discrete combinatorial methods. Rota's Entropy Theorem states that problems satisfying certain combinatorial properties are mathematically equivalent to scaled versions of Shannon Entropy. Furthermore, Shannon’s Coding Theorem guarantees that any system displaying Shannon-like entropy can be digitally encoded (as a series of yes/no questions). This implies that physics, at least in these entropic aspects, is representable as a computer program.

Electronic Graph Paper Theory fundamentally holds that space and time are discrete, space is "single occupancy" at the most fundamental level, and particles move through space stochastically (IID). With only those axioms, EGPT holds that everything else is constructively derivable - everything includes number theory, physics, and computer science. While EGPT does not necessarily assert that these axioms are the only way to describe the universe, it does assert that they are sufficient to describe the universe in a way that is computable and verifiable. Intuitively, EGPT posits that the universe is like a giant piece of graph paper where particles move around in a stochastic manner, and that this movement can be represented as a computer program. This program can then be used to derive all of the properties of the universe, including number theory, physics, and computer science.

Within the EGPT framework, the past is a recorded history of particle paths (computer program) and the future is a set of possible particle paths (an IID stochastic process). That is, the future is "predictable" in a probablistic sense, but not in a perfectly deterministic sense. What's more, when we say "predictable" we mean that the most likely possible futures are computable in "polynomial time" (P), or equivalently, we can categorize whether a possible future is "likely" or "unlikely" in polynomial time. This means that the universe is computable, and that the laws of physics can be expressed as computer programs.

## Core Concepts of EGPT's Number Theory, Complexity, and Physics Framework
In EGPT, number theory is just a representation of particle paths on the infinite grid. Within this context we'd like to have a parlance that mathematician number theorists, computer scientists, and physicists can all understand in an intuitive way. We will discuss these in progressively detailed ways but hope to start with very basic building blocks.

In EGPT, what physicsts call "particles" are what mathematicians call "stochastic" or "IID" events (independent identically distributed). Most people would call each IID event a "fair coin flip" and computer scientists would call the outcome of the flip a boolean value (aka bool, digital, or binary). So, particles move as if their next step was determined by a coin flip and their historical path is just a digital recording of the heads/tails results of each coin flip. 

In the realm of stochastic processes and probability theory, such a digital recording of the particle paths are typically called a "random walk" ... just a charting the net number of heads produced by a series of coin flips (net heads on Y axis, 1 flip per unit time on the X axis). 

Most of us conceptualize the counting numbers along a number line: 0, 1, 2, 3, ... and so on. Mathematicians call these the "Natural Numbers" and they are the most basic building block of number theory. Assuming a fair coin, a particle will return to the number line (form a Natural Number) when the heads and tails in the random walk are net 0, and we could therefore associate every Natural Number with the number of heads in symmetric path (symmetric means all heads then all tails, or, vice versa). For example, the path [1,1,0,0] is a symmetric path with 2 heads and 2 tails, which corresponds to the Natural Number 2. The path [1,1,1,0,0,0] is a symmetric path with 3 heads and 3 tails, which corresponds to the Natural Number 3. An Integer Number is a symmetric path can be ordered in two ways: all heads first or all tails first. For example, the path [1,1,0,0] can be symmetrically ordered as [1,1,0,0] (heads first) or [0,0,1,1] (tails first) but to distinguish them we can say that the first path is a "positive integer" and the second path is a "negative integer".

Physicists call these symmetric paths "waves" and each wave is characterized by a wavelength which, as we've just seen is also characterizable by the Natural Numbers as well as a list of 1's and 0's. To the computer scientist, they would call the symmetric path a "canonical binary representation" or a "sorted list of booleans" (List Bool) or a "digital tape" (a binary string). 

Since we want to make "clear" statements about things, from here on when we say "particle path" we will mean symmetric paths, or, paths built from symmetric paths. In any case, we can think of it all as just counting the number of heads in a particular path, and this is the most basic building block of number theory, computer science, and physics.

Very quickly we see how mathematical operations on the paths are visually intuitive. For example, adding [1,1,0,0] and [1,1,1,0,0,0] gives us [1,1,1,1,1,0,0,0,0,0] which is the same as the Natural Number 5. This is because we can think of the paths as being "concatenated" together and then made symmetrical again by sorting. Concatenation and sorting are fundamental operations in computer science and mathematics that allows us to combine two or more sequences into one. In this case, we are concatenating two symmetric paths to form a new symmetric path. Similarly, we can think of subtracting paths as removing one path from another, which is also visually intuitive. For example, subtracting [1,1,0,0] from [1,1,1,0,0,0] gives us [1,0] which is the same as the Natural Number 1. 

Multiplication of paths A and B can be thought of as concatenating A with itself once for every head in B. For example, multiplying [1,1,0,0] by [1,1,1,0,0,0] gives:
[1,1,0,0] + [1,1,0,0] + [1,1,0,0] = [1,1,1,1,1,1,0,0,0,0,0,0] which is the same as the Natural Number 6. We also see that multiplication is commutative, i.e., the order of the paths does not matter.

For brevity, rather than writing out the full paths with the zeros, we can just write the number of heads in the path. For example, we can write [1,1,0,0] as [1,1] or simply 2 and [1,1,1,0,0,0] as [1,1,1] or 3. This gives us a more compact representation of the paths and allows us to easily perform mathematical operations on them.

For each of physicists, mathematicians, and computer scientists a key motivation is to calculate the "end state" of something. In physics, we might want to know the final positions of particles, atoms, or planets after a series of interactions. In mathematics, we might want to know the final value of a function or the solution to an equation. In computer science, we might want to know the final output of a program or algorithm. Within the EGPT framework, we now have an intuitive senses that calculating the end state of particles (physics) is like counting heads in a random walk on the number line (mathematics) or counting the number of 1's in a binary string (computer science). 

The mathematical branch dedicated to counting problems is called "Combinatorics" and historically it has been distinct from both number theory and computer science. However, within the EGPT framework, combinatorics is just a way of counting the number of heads in a random walk or the number of 1's in a binary string. This means that combinatorics is just another way of representing particle paths and their end states.

## Some Definitions For Counting Problems in EGPT
In EGPT, we can define some basic concepts that will help us understand the relationships between particle paths, number theory, and computer science.

"Prime" paths are paths which can not be composed by multiplication except by multiplying with 1. For example, [1,1] is a prime path and [1,1,1] is a prime path, but [1,1,1,1] is not a prime path since it is the concatenation of [1,1] to itself. PrimePaths are therefore fundamental building blocks of all paths such that any path can be viewed as a concatenation of sub-component PrimePaths even if the sub-component is the PrimePath itself. 

Real paths are just the set of all possible paths that can be formed by concatenating PrimePaths. If one visualized an infinite binary tree where each node is a point on the number line, then the Real paths would be all the paths that can be formed by traversing the tree from the root node to any leaf node. For an infinite binary tree where there are n leaf nodes, there are 2^n possible "real" paths to that node. Mathematicians call the n leaf nodes "countably infinite" and anything that grows exponentially with respect to an infinite n, such as 2^n, is called "uncountably infinite" or the "continuum". 

Perhaps not-coincidentally, how mathematics defines the Real Numbers (2^n) is also how computer scientists define non-computable programs (i.e., exponential time complexity). This is worth saying in a few different ways to emphasize the point:
- Quantum / Particle Physics = The Set of All Possible Paths (All Possible "Futures") =  Computer Science Non-computable = Exponential Time Complexity = Combinatorics "power set" 2^n = Mathematical Real Numbers = Mathematical Continuum
- Computer Science Computable = Polynomial Time Complexity = Fixed length digital tape = actual physics particle paths taken = recorded outcomes of coin flips 

One would then quickly ask how the uncountably infinite set of all possible futures in physics and the non-computable computer science relates to the computable and countable? The answer lies in the "law of large numbers" as it relates to counting problems for coin-flips. Very intuitively, if you flip a coin only 3 times, the outcome is very uncertain and possibly random looking. However, if you flip a coin one million times, the outcome is very predictable and will be very close to 500,000 heads and 500,000 tails. However, with some exceptionally low probability, it is possible that you could get 400,000 heads and 600,000 tails. This is the "law of large numbers" in action. The law of large numbers states that as the number of trials increases, the probability of the outcome converging to the expected value increases. In other words, as we increase the number of coin flips, the probability of getting a certain number of heads or tails approaches a limit.

What we need then is a way to analyze counting problems for very large numbers of coin flips, or equivalently, very large numbers of particle paths. This is where combinatorics comes in, particularly Prof. Gian-Carlo Rota's Entropy Theorem and the Partition Theory on which it is based. 

--- DEFINITIONAL BRAINSTORMS FOR Counting ---
H(t : Nat, p : ParticlePath) := h -- where h is the number of heads in a path p at time t (i.e. the first t elements of the ParticlePath)

Algorithm = recorded ParticlePath (List Bool) ... a canonical Int

ParticlePosition = given (t : Nat) (path : ParticlePath) := t --where t is the time (number of coinflips recorded) on the particle's path where the origin is time 0. I.e. it is the first t elements of the  of the ParticlePath (which, since ParticlePath is Int in canonical form (List Bool), ParticlePath is just another Int, with Nat magnitude t)

PathProgram (Int paths) as a data structure (List, concat, etc.) of Algorithm's (single paths) ... List Algorithm

MathFunction as mappings to end positions. Therefore MathFunction := List ParticlPath := List Nat := List Int := List Algorithm := PathProgram

ParticlePosition := List ParticlePosition

PartitionFunction (partitionSize : Nat, ParticlePosition)

## Computing the Future Using Rationals As Partition Functions: Uniform in the Microstates

The Galton board, a device where beads cascade through a triangular array of pegs, offers a tangible way to understand the difference between uniform and normal distributions and the statistical concept of microstates.

### The Normal Distribution: The Familiar Bell Curve

In a standard Galton board, the pegs are arranged in a triangle. As a bead descends, it strikes a peg at each level and has a 50/50 chance of falling to the left or right. The final distribution of beads in the bins at the bottom forms a **normal distribution**, famously known as the "bell curve."

Here's why this happens:

* **Many Paths to the Center:** There are many different paths a bead can take to land in one of the central bins. For a bead to reach a central bin, it needs to take a roughly equal number of left and right turns.
* **Few Paths to the Edges:** Conversely, for a bead to end up in a bin at the far edges, it must take a highly specific and improbable sequence of turns (e.g., all left turns or all right turns).

This difference in the number of possible paths leads to the characteristic bell shape: the central bins, with the most possible paths, collect the most beads, while the outer bins, with the fewest paths, collect the least.

---

### The Normal Distribution is "Uniform in Its Microstates"

The key to understanding this statement lies in the distinction between a **macrostate** and a **microstate**.

* **Macrostate:** This is the overall, observable outcome. In the Galton board, the final distribution of beads in the bins—the bell curve—is the macrostate. We don't care about the specific journey of each bead, only the final count in each bin.

* **Microstate:** This is the specific path that an individual bead takes to reach a bin. Each unique sequence of left and right turns is a distinct microstate.

The statement that the normal distribution is "uniform in its microstates" means that **every single possible path (microstate) has the exact same probability of occurring.**

For a board with *N* rows of pegs, any specific path consists of *N* left or right turns. The probability of any single path is simply $(1/2)^N$. For example, the path "Left-Right-Left" is just as likely as "Left-Left-Left."

The reason the normal distribution (the macrostate) is not uniform is that different numbers of microstates lead to each final position. While each individual path is equally likely, the central bins are the destination for a much larger number of these equally likely paths.

In essence, the apparent non-uniformity of the bell curve arises from a deeper, underlying uniformity at the level of individual probabilistic events.

### Paths are uniform in their microstates, but the macrostate (System State) is not uniform
Thinking of the Galton board, we could think of the collection bins at the bottom as the "System State" of the board and ask questions like whether a particular bin is occupied or not, how many particles are in each bin, or what the distribution of particles looks like. The System State is a collection of all the microstates (individual particle paths) that lead to the final distribution of particles in the bins.

Furthermore, since all paths are equally likely, 

Since we want to compute the future of systems of particles as if we were walking a binary computer tape, and furthermore, since the law of large numbers is our bridge to doing so, we will want convenient ways to talk about large sets of particle paths. We can think of the evolution of a system of particles as a series of discrete time steps just like the Galton board levels, where each step is a coin flip/ peg that determines the next position of the particle ... i.e. the set of particle paths is the definition of state of the system at a given time (or equivalently, the particle positions if we repeat the process for each particle).

### Computer Programs as Finite Samples From the IID Source (I.e. Samples are a set of *actual* Particle Paths)
We have already said that particle paths are equivalent to a "digital tape" that records the outcomes of the coin flips, and the paths can be represented as binary strings (List Bool) where each bit represents the outcome of a coin flip (heads or tails). Computer Science, built on the framework of Turing Machines, definitionally finds our List Bool equivalent to the "tape" of a replayable by a Universal Turning Machine and the UniversalTuringMachine itself represents a replay mechanism for the uncountably infinite set of all tapes. Previously we have said that the set of all particle paths is equivalent to the set of all possible outcomes of a stochastic process and we also said that "PrimePaths" are the fundamental building blocks of all paths. It therefore follows that any Computer Program (concatenation of List Bool which are particle paths) ... so we can think of a Computer Program made up of PrimePaths as a set of particle paths that can be executed in a sequence to produce a final output. Computer Scientists would call these PrimePaths "Symbols" or "words" in a formal "Language". In short, an IIDSource of particles will produce the every possible PathProgram (ParticlePath's) and also the Language composed of a countably infinite set Symbols.  

In this framework, we can think of a computer program as a set of recorded particle paths, where each path is a sequence of coin flips that determines the movement of a particle through space over time. 

### SystemStates As Probabilistic Functions

Intuitively (and formally) every position on the infinite grid is reachable by a particle path from time 0 to t as t has no bound - this is in fact our definition of the Real Numbers as the Continuum. The set of all particle paths is the set of all possible outcomes of a stochastic process, and this set is uncountably infinite. 

In our formalization, 

### Concepts that will be made more precise include:

**Discrete Space**: The universe is a discrete grid of points (the graph paper) on which "particles" move.

**Particles**: Particles are represented as points on this grid, each occupying a unique position.

**Binary/Digital Grid Point Occupancy**: The state of a particle (e.g., its position) is represented by binary (Boolean) values indicating whether a point is occupied or not.

**Discrete Time**: Time is also discrete and monotonically increasing, with each time step representing a change in the state of the universe.

**Stochastic Movement**: Particles move through space in a stochastic manner - as if by a coin flip - with each step being independent and identically distributed (IID).

**Particle Paths = Random Walk = List Boolean = Digital Tape = Algorithm:** The path of a particle over time (from 0 to t) through space is represented as a t length list of boolean values (a binary string or "tape"), where each value boolean value in the tape records the stochastic choice made by the particle. We can arbitrarily say that true = up and false = down, or heads and tails, or 1 and 0. The path of a particle is thus a binary string of length t, which can be interpreted as a natural number in base 2. This number can also be interpreted as an Algorithm that describes the particle's movement through space over time.


**Natural Numbers**: Ordered particle paths to position on a "left,top" origin electronic graph: For a given particle which makes one coin flip decision every tick of time t, a Natural Number is number coin flips (ticks of time), a Natural Number is the number of heads. For example, at t=1 there could 0 or 1 heads, t=2, there could 0,1,2 heads, t=3, 0,1,2,3 heads etc.. We can uniquely denote a single natural number as a "tape" of t coin flip outcomes where the heads are ordered first. A convenient visual representation of this is plotting the Natural Number paths on the left, top grid. For example, for a particle following its random walk coin flip process on a left, top oriented electronic grid (0,0 is left, top) one could label stochastic movement choices as heads=right=true, tails=down=false. To give a unique label to every grid position we only need to count the number of heads given t coin flips. For example, given t=3 (three coin flips) where there have been 2 heads and 1 tail, the natural number "2" represents the position of the particle at time t=3 and the order of the coin flips does not matter. Since the order didn't matter our canonical representation of ordering the heads first will always give us the correct particle at position of (2,1) on the grid.



**Integer Numbers**: Ordered paths to particle positions on the centered grid: Whereas the Natural Numbers count number of heads as a terser representation of the entire particle path, the Integer Numbers are an equivalent representation of the Natural Numbers with the additional convention that the path is ordered according to the first bit. For example, if the first bit is 1 (heads) then all heads will be at the front of the List Bool. If the first bit is tails, then all tails will be at front followed by all heads such that heads + tails = time. It is then intuitively (and formally) clear that the Integer Numbers are equivalent to the Natural Numbers in the sense that the same end point in a particle path is reached regardless of whether the heads or tails decisions come first. The transformation between the two is called a "bijection" and the existence of the bijection is clear from the physical path intuition.




Let H(t,p) = h be how we denote the number of heads in a path p over time t.

the function H is partitionable over t s.t. H from 0 to t = sum(H(i,p)) for sum(i) = t

 ...

Remembering that n = H(t,p), t = (h,t) is a "coordinate" (e.g. for positive number of heads for a coin flipped t times),

IDEA For Computational Complexity = Physics Entropy = Information Theory Entropy = Rota's Entropy Theorem:
H is a function that tells us how many recorded decisions were made (answers to yes/no questions on the binary source) for some t length finite sample of the source. This is equivalent to the 1's  necessary to represent a computer program using List Bool canonical ints (a satisfying state of a system = the state of a set of particles at time t) = sum(1 to n){1's in each path p for n paths} = sum(1 to n){H(t,p)} = sum(1 to n){h} = n * h

### Assessing 2 Cases: A program of unknown computation time (t), and a program of unknown space (n)
In the context of Rota's Entropy Theorem, we can think of the number of heads in a path as a measure of the "information content" of the path.

In the time domain, noting that the number of possible paths is 2^(t) and the path length is t,for each path p, we can say that the number of 1's in the path is  h <= path length <= log2(2^t) 

In the space domain, we can say that a satisfying state of a system with n particles has at most n positions (n paths) and, if we were to return those particles along the path back to the origin (the IIDSource), then the number of 1's in the path is h <= log2(n).

