# Prime Numbers

This project uses formal verification to prove properties of prime numbers. 
The project is written in Scala and uses the Stainless library to prove theorems.

## Note

This project was initially created using Dafny,
but we decided to switch to Stainless because of the better support for Scala.

This rewriting process is still ongoing, 
and we are currently working on the properties of prime numbers.

## Prime Properties

### Division and Modulo Properties

[Properties of Division and Modulo](./modulo.md)

In this paper, we proof the following properties of division and modulo:


```math
\begin{align*} \\
a >= 0 \text{ and } b > a \implies a \text{ div } b  & = 0 \\
a >= 0 \text{ and } b > a \implies a \text{ mod }  b & = a \\
b \text{ mod } b                   & = 0 \\
b \text{ div } b                   & = 1 \\
( a + b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
( a - b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
(a \text{ mod } b) \text{ mod } b  & = a \text{ mod } b \\
(a + b) \text{ div } b             & = (a \text{ div } b) + 1 \\
(a - b) \text{ div } b             & = (a \text{ div } b) - 1 \\
(a + b \cdot m ) \text{ div } b    & = (a \text{ div } b) + m \\
(a - b \cdot m ) \text{ div } b    & = (a \text{ div } b) - m \\
(a + c) \text{ div } b             & = (a \text{ div } b) + (c \text{ div } b) + (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
(a - c) \text{ div } b             & = (a \text{ div } b) - (c \text{ div } b) + (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
(a + c) \text{ mod } b             & = ((a \text{ mod } b) + (c \text{ mod } b)) \text{ mod } b \\
(a - c) \text{ mod } b             & = ((a \text{ mod } b) - (c \text{ mod } b)) \text{ mod } b \\
(a + c) \text{ mod } b             & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } c) \\
(a - c) \text{ mod } b             & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } c) \\
\end{align*}
```

## Running the Formal Verification

### Running Locally

- Scala 3.4.0
- Just 1.16.0
- JEnv 0.5.7
- Java 21
- Stainless 0.9.8

```bash
just verify
```
### Running on Docker

- Just 0.5.7
- docker 20.10.16

```bash
just verify-docker
```

