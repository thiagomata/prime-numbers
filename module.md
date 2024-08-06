# Division and Module

Given integers $dividend$ and $divisor$ where $divisor \neq 0$, the division algorithm determines integers $quotient$ and $remainder$ such that:

$$
\forall \text{ } dividend, divisor \in \mathbb{N}, \text{ where } divisor\neq 0 
$$

$$
\exists ! \
\text{quotient} = \left\lfloor \frac{\text{dividend}}{\text{divisor}} \right\rfloor \implies  
$$

$$
dividend = divisor \cdot quotient + \text{remainder}, \text { where } 0 \leq \text{remainder} < |b|, 
$$

$$
dividend \text{ mod } divisor = remainder, 
$$

$$
dividend \text{ div } divisor = quotient. 
$$


## Some Important Properties

### Unique Remainder Property in Integer Division

There is only one single remainder value for every $a, b$ pair.

$$
\forall a, b \in \mathbb{N}, \exists ! \text{ remainder } r \text{ such that } 0 \leq r < |b| \text{ and } a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r 
$$


### Modulo Identity

The modulo of every number by itself is zero.

$$
\forall n \in \mathbb{N}, n \text{ mod } n = 0
$$

### Modulo Addition

Adding the divisor to the dividend do not change the mod result.

$$
\forall a,b \in \mathbb{N}, (a + b) \text{ mod } b = a \text{ mod } b
$$

### Modulo Multiplication

Recursively applying the Modulo Addition Property, we can prove that:

$$
\forall a,b,m \in \mathbb{N}, (a + m \cdot b) \text{ mod } b = a \text{ mod } b
$$

### Div Addition Propert

Adding the divisor to the dividend increase the div result by one.

$$
\forall a,b \in \mathbb{N}, (a + b) \text{ div } b = (a \text{ div } b ) + 1
$$


Therefore:

$$
\forall a,b,m \in \mathbb{N}, (a + m \cdot b) \text{ div } b = (a \text{ div } b ) \cdot m
$$


### Modulo Result for Small Dividend

If the dividend is smaller than the divisor, the result of the modulos operation should be the dividend value.

$$
\forall a,b \in \mathbb{N}, \text{ where } a < b \implies a \text{ mod } b = a
$$

### Modulo Idempotence

$$
\forall a,b \in \mathbb{N}, a \text{ mod } b = ( a \text{ mod } b ) \text{ mod } b
$$

