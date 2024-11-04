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

