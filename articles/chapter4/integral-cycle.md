# Verificação Formal de Propriedades de Integrais de Ciclos a partir de Primeiros Princípios

**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)
**GitHub:** [@thiagomata](https://github.com/thiagomata)
**Licença:** [CC BY 4.0](../LICENSE)<br>
**Publicado:** [Zenodo:10.5281/zenodo.22868423](https://doi.org/10.5281/zenodo.22868423)

## Resumo

<div align="justify">
<p style="text-align: justify">
Em artigos anteriores, definimos Listas limitadas, Integrais de Listas e Ciclos ilimitados de Inteiros
desde o início, usando apenas construções centrais de tipos e recursão,
sem exigir conhecimento prévio das coleções de Scala.
A partir disso, provamos e verificamos formalmente algumas propriedades relacionadas a essas estruturas.
Este artigo usa esse material como fundamento para definir Integrais de Ciclos por meio de duas
apresentações: a definição recursiva canônica `CycleIntegral` e uma definição em forma fechada
`ModCycleIntegral`.
Para ambas as apresentações, verificamos formalmente a propriedade da soma (a integral é igual
à soma cumulativa do ciclo) e a propriedade do passo (a diferença entre valores consecutivos
é igual ao elemento correspondente do ciclo) usando o sistema de verificação Stainless.
Também provamos que as definições recursiva e modular são extensionalmente equivalentes.
Todas as propriedades são expressas e provadas dentro de um arcabouço mínimo, usando apenas
aritmética elementar, recursão e código Scala puro.
Este trabalho conecta fundamentos matemáticos e verificação executável,
oferecendo uma abordagem autocontida e verificável para raciocinar sobre acumulações periódicas infinitas.
 </p>
</div>

<a id="1-introduction"></a>
## 1. Introdução

Ciclos são um conceito poderoso em ciência da computação e matemática, representando listas ilimitadas que repetem uma sequência finita de elementos. Quando integramos ciclos, obtemos uma lista de somas cumulativas com algumas propriedades únicas que exploraremos neste artigo.

```math
\begin{aligned}
L &= [l_0, l_1, l_2, \ldots, l_{n-1}]  \mid &l_n &\in 𝕊, L \in 𝕃\\
\end{aligned}
```

```math
\begin{aligned}
\text{Cycle}(L)               &= [l_0, l_1, l_2, \ldots, l_{n-1}, l_0, l_1, \ldots] \\
                              &= [v_0, v_1, v_2, \dots] \mid &v_i &= L[i \text{ mod } n] \\
\text{Integral}(L, init)      &= [y_0, y_1, y_2, \ldots, y_{n-1}] \mid &y_k &= \sum_{i=0}^{k} x_i + init \\
\text{CycleIntegral}(L, init) &= [w_0, w_1, w_2, \ldots] \mid          &w_k &= \sum_{i=0}^{k} \text{Cycle}(L)_i + init
\end{aligned}
```

Neste artigo, apresentamos uma definição discreta de Integral de Ciclo
sobre listas finitas de inteiros, definida recursivamente, e verificamos algumas de suas propriedades usando o sistema Stainless.
Nossa abordagem segue uma filosofia de conhecimento prévio zero, construindo sobre uma base já
verificada para estruturas recursivas de listas, integrais e somatórios.
O resultado é uma implementação verificada, desde o início, da integral de ciclo,
adequada como fundamento para raciocínio numérico de nível mais alto sobre listas ilimitadas.

Este artigo verifica:

- Duas definições equivalentes: recursiva e baseada em módulo — [§3.1](#31-recursive-cycle-integral)–[3.3](#33-equivalence-of-definitions)
- Propriedades centrais: próxima posição, mesma diferença após um ciclo, soma de valores modulares, crescimento estrito, positividade, geração pelo ciclo unitário — [§4.1](#41-next-position)–[4.6](#46-unit-cycle-generation-of-consecutive-integers)
- Propriedades persistentes e periódicas: como os resíduos de uma integral de ciclo fixa se comportam indefinidamente e como ela avança por períodos completos — [§5.1](#51-cycle-period-shifts)–[5.6](#56-cycle-residue-classification)
- Derivação de novas integrais de ciclos: expansão, deslocamentos de índice, rotação, filtragem de sobreviventes e reconstrução baseada em mesclagem — [§6.1](#61-x-fold-cycle-expansion)–[6.10](#610-filtered-result-has-no-multiples)

### Trabalhos relacionados

A Mathlib do Lean fornece uma teoria formal geral de funções periódicas. Ela prova
que uma função periódica permanece periódica sob múltiplos inteiros de um período,
e que uma soma finita de funções periódicas é periódica [[6]](#ref6). A Mathlib
também representa um ciclo finito como uma lista módulo rotação cíclica [[7]](#ref7).
Esses resultados dão contexto formal para a estrutura de período finito e deslocamento
usada pela construção presente.

Este artigo estuda um objeto diferente: a integral cumulativa de uma lista periódica concreta
de inteiros. Seus resultados verificados centrais são a equivalência entre uma
integral recursiva e uma forma fechada por quociente e resto, junto com as
propriedades resultantes de passo, período completo, resíduo e reconstrução. Assim, os
desenvolvimentos existentes sobre periodicidade e ciclos finitos enriquecem o
contexto sem substituir esta prova de integral de ciclo em duas apresentações.

## 2. Preliminares

Reutilizamos várias operações básicas de listas, ciclos e integrais, bem como suas propriedades verificadas, dos artigos complementares
[Using Formal Verification to Prove Properties of Lists Recursively Defined](https://rxiverse.org/abs/2609.0023) [[1]](#ref1),
[Formal Verification of Discrete Integration Properties from First Principles](https://doi.org/10.5281/zenodo.22746792) [[2]](#ref2),
e [Formal Verification of Cyclic Lists](https://doi.org/10.5281/zenodo.22865441) [[3]](#ref3).
Também reutilizamos algumas propriedades de módulo definidas e verificadas anteriormente no artigo
[Division and Modulo from Recursive Normalization](http://ai.viXra.org/abs/2609.0009) [[4]](#ref4).

Esses artigos também definiram e verificaram suas propriedades usando a mesma metodologia de conhecimento prévio zero,
e são tratados aqui como primitivas fundamentais.

## 3. Definições de Integral de Ciclo

A integral de ciclo estende a integral finita a sequências repetitivas ilimitadas. Duas definições equivalentes são provadas.

- Recursiva: recorrência sobre a posição no ciclo — [§3.1](#31-recursive-cycle-integral)
- Modular: forma fechada usando `div` e `mod` — [§3.2](#32-modulo-cycle-integral)
- As duas definições são extensionalmente equivalentes — [§3.3](#33-equivalence-of-definitions)

```math
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃, n = |L| \\
\text{CycleIntegral}(L, init) := [w_0, w_1, w_2, \ldots]
```

```math
\begin{aligned}
0 \leq i < n \implies w_i = \sum_{j=0}^i L_j + init \quad &\text{[Propriedade da Soma]} \\
i > 0 \implies  \ w_i - w_{i-1} = L_{(i \text{ mod } n)}
\quad &\text{[Propriedade do Passo]} \\
\end{aligned}
```

<a id="31-recursive-cycle-integral"></a>
### 3.1 Integral de Ciclo Recursiva

```math
\begin{aligned}
\text{RecCycle}(L) &= [v_0, v_1, \dots] \mid v_i =
\begin{cases}
  L[i] & i < n \\
  v_{i - n} & i \geq n
\end{cases} \\
\text{RecCycleIntegral}(L, init) &= [w_0, w_1, \dots] \mid w_i =
\begin{cases}
  init + w_0 & i = 0 \\
  v_i + w_{i - 1} & i > 0
\end{cases}
\end{aligned}
```

**Equivalência do Ciclo Recursivo**: o Ciclo Recursivo é equivalente ao Ciclo Modular, como provado no artigo [Formal Verification of Cyclic Lists](https://doi.org/10.5281/zenodo.22865441) [[3]](#ref3).

```math
\begin{aligned}
RecCycle(L)_i &=  ModCycle(L)_i \quad &\text{[Equivalência de Ciclos]} \\
  &= L_{(i \text{ mod } n)} \quad &\text{[Definição do Ciclo Modular]} \\
\end{aligned}
```

**Propriedade da Soma**:

```math
\begin{aligned}
v_0  &= L_0  \quad &\text{[Caso Base]} \\
&= L_{(0 \text{ mod } n)} \quad &\text{[Pela Propriedade Modular]} \\
&= \sum_{j=0}^0 L_j \quad &\text{[Reindexação do Somatório]} \\
\end{aligned}
```

```math
\begin{aligned}
i < n \implies \\
w_0 &= init + v_0 \quad &\text{[Caso Base]} \\
&= init + \sum_{j=0}^i L_j  \quad &\text{[Reindexação do Somatório]} \\
i > 0 \implies \\
w_i &= init + v_0 + \sum_{j=1}^i v_j \quad &\text{[Pela Definição]}\\
&= init + v_0 + \sum_{j=1}^i L_j \quad &\text{[Propriedade Modular de Valores Pequenos]} \\
&= init + \sum_{j=0}^i v_j \quad &\text{[Reindexação do Somatório]} \\
\therefore w_i &= init + \sum_{j=0}^i L_j \quad &\text{[C.Q.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.1; a prova completa está vinculada na referência ao código-fonte.

**Propriedade do Passo**:

```math
\begin{aligned}
w_i - w_{i-1} &= v_i + w_{i-1} - w_{i-1} \quad &\text{[Pela Definição]} \\
&= v_i \quad &\text{[Simplificação]} \\
&= L_{(i \text{ mod } n)} \quad &\text{[Substituição]} \\
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertDiffEqualsCycleValue
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.2; a prova completa está vinculada na referência ao código-fonte.

<a id="32-modulo-cycle-integral"></a>
### 3.2 Integral de Ciclo Modular

```math
\begin{aligned}
&\text{ModCycle}(L)_i &:= L_{(i \text{ mod } n)} = [w_0, w_1, \dots ] \\
&I_k &:= \sum_{j=0}^{k} L_j \quad (0 \leq k < n) \quad &\text{[Integral de L]} \\
&S &:= I_{n-1} \quad &\text{[Soma de um ciclo completo]} \\
&\text{ModCycleIntegral}(L, init)_i &:= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init
\end{aligned}
```

**Propriedade da Soma**:

```math
i < n \implies w_i = \sum_{j=0}^i L_j + init \quad \text{[Afirmação a Provar]}
```

```math
\begin{aligned}
i < n \implies  \\
i \text{ div } n
      \quad &= 0 \quad
      &\text{[Pela Propriedade da Divisão de Valores Pequenos]} \\
w_i &= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init \quad
      &\text{[Definição]} \\
&= 0 \cdot S + I_i + init \quad &\text{[Substituição]} \\
&= \sum_{j=0}^i L_j + init \quad &\text{[Pela definição de } I_i]
\end{aligned}
```

```math
\therefore \
\forall \ i < n,\quad w_i = \sum_{j=0}^i L_j + init \quad \text{[C.Q.D.]}
```

Esta propriedade é verificada em [
ModCycleIntegralProperties::assertFirstValuesMatchIntegral
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.3; a prova completa está vinculada na referência ao código-fonte.

**Propriedade do Passo**:

```math
w_i - w_{i-1} = L_{\, i \text{ mod } n}, \quad i>0,\, n>0
\quad \text{[Afirmação a Provar]}
```

**Caso $i \text{ mod } n > 0$:**

```math
\begin{aligned}
&i \text{ mod } n &= ((i-1) \text{ mod } n) + 1 &&\text{[Pelas Propriedades Modulares]} \\
&i \text{ div } n &= (i-1) \text{ div } n &&\text{[Pelas Propriedades de Divisão]} \\
&w_i &= (i \text{ div } n)\,S + I_{\,i\text{ mod } n} + init &&\text{[Definição]} \\
     &&= (i-1 \text{ div } n)\,S + I_{\,((i-1)\text{ mod } n)+1} + init &&\text{[Propriedade div/mod]} \\
&w_{i-1} &= (i-1 \text{ div } n)\,S + I_{\, (i-1)\text{ mod } n} + init &&\text{[Definição]} \\
&w_i-w_{i-1} &= I_{\,((i-1)\text{ mod } n)+1} - I_{\, (i-1)\text{ mod } n} &&\text{[Cancelamento]} \\
    &&= \Big(\sum_{j=0}^{(i-1)\text{ mod } n} L_j + L_{((i-1)\text{ mod } n)+1}\Big)
       - \sum_{j=0}^{(i-1)\text{ mod } n} L_j &&\text{[Expandir soma]} \\
    &&= L_{((i-1)\text{ mod } n)+1} &&\text{[Cancelamento]} \\
    &&= L_{\,i \text{ mod } n} &&\text{[Propriedade modular]}.
\end{aligned}
```

**Caso $i \text{ mod } n = 0$:**

```math
\begin{aligned}
w_i &= (i \text{ div } n)\,S + L_0 + init
&&\text{[Definição]} \\
w_{i-1} &= (i \text{ div } n -1)\,S + I_{\,n-1} + init
&&\text{[Propriedade div/mod]} \\
w_i-w_{i-1}
    &= (i \text{ div } n)\,S + L_0 + init
       - \big((i \text{ div } n -1)\,S + I_{\,n-1} + init\big)
&&\text{[Substituição]} \\
    &= S + L_0 - I_{\,n-1}
&&\text{[Simplificação]} \\
    &= L_0
&&\text{[Como } S = I_{\,n-1}] \\
    &= L_{\,i \text{ mod } n}
&&\text{[Propriedade modular]}.
\end{aligned}
```

```math
\therefore \
w_i - w_{i-1} = L_{\, i \text{ mod } n}, \quad \forall \ i > 0 \quad \text{[C.Q.D.]}
```

Esta propriedade é verificada em [
ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.4; a prova completa está vinculada na referência ao código-fonte.

<a id="33-equivalence-of-definitions"></a>
### 3.3 Equivalência das Definições

A equivalência não trivial provada aqui é entre a definição recursiva `CycleIntegral`
e a definição em forma fechada `ModCycleIntegral`.

```math
\begin{aligned}
\text{CycleIntegral}(L, init)
&= \text{ModCycleIntegral}(L, init) \\
&= [w_0, w_1, w_2, \ldots] \mid w_i =& \sum_{j=0}^i L_{(j \text{ mod } n)} + init \ \blacksquare
\end{aligned}
```

Esta propriedade é verificada em [
ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.5; a prova completa está vinculada na referência ao código-fonte.

## 4. Propriedades Centrais Verificadas

As propriedades fundamentais da integral de ciclo que valem para toda posição.

- Próxima posição: $CI_{i+1} = CI_i + Cycle(L)_{i+1}$ — [§4.1](#41-next-position)
- Deslocamento por ciclo completo: adicionar um período de ciclo avança pela soma total — [§4.2](#42-same-difference-after-full-cycle)
- Soma de valores modulares: a definição modular coincide com a soma da lista — [§4.3](#43-sum-of-mod-values-as-list)
- Crescimento estrito: valores-base positivos forçam uma integral estritamente crescente — [§4.4](#44-cycle-integral-strictly-increasing)
- Positividade: um início não negativo e valores-base positivos mantêm a integral positiva em toda posição — [§4.5](#45-cycle-integral-positivity)
- Geração pelo ciclo unitário: o ciclo unitário `[1]` enumera os inteiros consecutivos, em ordem estritamente crescente — [§4.6](#46-unit-cycle-generation-of-consecutive-integers)

<a id="41-next-position"></a>
### 4.1 Próxima Posição

Para qualquer posição positiva, a integral de ciclo nessa posição é igual ao valor anterior mais o elemento atual do ciclo.

```math
\forall \ i > 0: \ CI(L, init)_i = CI(L, init)_{i-1} + Cycle(L)_i
```

Isso segue diretamente da definição recursiva de `CycleIntegral`.

Esta propriedade é verificada em [
CycleIntegralProperties::assertNextPosition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

<a id="42-same-difference-after-full-cycle"></a>
### 4.2 Mesma Diferença Após um Ciclo Completo

A diferença entre valores consecutivos é invariante ao adicionar o tamanho de um ciclo completo às duas posições.

```math
\forall \ i \geq 0: \ CI(L, init)_{i+1} - CI(L, init)_i = CI(L, init)_{i+size+1} - CI(L, init)_{i+size}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertSameDiffAfterCycle
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.6; a prova completa está vinculada na referência ao código-fonte.

<a id="43-sum-of-mod-values-as-list"></a>
### 4.3 Soma de Valores Modulares como Lista

A integral de ciclo em qualquer posição é igual à soma de uma lista construída que contém o valor inicial e todos os valores do ciclo até essa posição (usando indexação modular para posições além de um ciclo).

```math
\forall \ i \geq 0: \ CI(L, init)_i = \text{sum}([init] + [Cycle(L)_0, Cycle(L)_1, \dots, Cycle(L)_i])
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.7; a prova completa está vinculada na referência ao código-fonte.

<a id="44-cycle-integral-strictly-increasing"></a>
### 4.4 Integral de Ciclo Estritamente Crescente

Quando o valor inicial é não negativo e todo valor da lista-base é
positivo, a integral de ciclo é estritamente crescente: uma posição posterior
sempre produz um valor maior.

```math
\begin{aligned}
init \geq 0 \;\land\; (\forall x \in L,\ x > 0) \;\land\; b > a \implies
\text{CycleIntegral}(L, init)_b > \text{CycleIntegral}(L, init)_a
\end{aligned}
```

**Prova.** Fazemos indução sobre $b-a$. O caso base é um passo positivo; o
passo indutivo adiciona mais um valor positivo do ciclo.

```math
\begin{aligned}
b=a+1 &\implies CI_b-CI_a=\text{Cycle}(L)_b>0 &&\text{[§3.1 e positividade do ciclo]} \\
       &\implies CI_b>CI_a, \\
CI_{b-1}>CI_a,\quad CI_b-CI_{b-1}=\text{Cycle}(L)_b>0
       &\implies CI_b>CI_{b-1}>CI_a \\
\therefore\ CI_b &> CI_a.
  \quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertCycleIntegralIncreasing
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

<a id="45-cycle-integral-positivity"></a>
### 4.5 Positividade da Integral de Ciclo

Quando o valor inicial é não negativo e todo valor da lista-base é
positivo, a integral de ciclo é positiva em toda posição.

```math
\begin{aligned}
init \geq 0 \;\land\; (\forall x \in L,\ x > 0) \implies
\text{CycleIntegral}(L, init)_i > 0
\end{aligned}
```

**Prova.** Na primeira posição, o valor inicial não negativo e um
valor positivo do ciclo produzem uma integral positiva. Toda posição posterior adiciona
mais um valor positivo do ciclo.

```math
\begin{aligned}
CI_0 &= init+\text{Cycle}(L)_0>0, \\
CI_{i-1}>0,\quad CI_i-CI_{i-1}=\text{Cycle}(L)_i>0
  &\implies CI_i>0 \\
\therefore\ CI_i &> 0.
  \quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertCycleIntegralPositive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

<a id="46-unit-cycle-generation-of-consecutive-integers"></a>
### 4.6 Geração de Inteiros Consecutivos pelo Ciclo Unitário

O ciclo não vazio mais simples é o ciclo unitário `[1]`: todo passo adiciona exatamente
um. Sua integral de ciclo enumera os inteiros consecutivos começando após
o valor inicial — o fluxo de candidatos que a peneira de primos filtra nos
artigos posteriores. Como cada passo contribui exatamente um, a integral tem
uma forma fechada exata em toda posição, e o crescimento estrito decorre disso
como a instância de ciclo unitário de [§4.4](#44-cycle-integral-strictly-increasing).

```math
\begin{aligned}
init \geq 0 \implies \text{CycleIntegral}([1], init)_i = init + i + 1
\end{aligned}
```

**Prova.** Indução sobre $i$.

**Caso Base** ($i = 0$):

```math
\begin{aligned}
\text{Cycle}([1])_0 &= 1 &&\text{[Ciclo Unitário]} \\
CI_0 &= init + \text{Cycle}([1])_0 &&\text{[Pela Definição]} \\
&= init + 1 &&\text{[Substituição]}
\end{aligned}
```

**Passo de Indução** ($i > 0$):

```math
\begin{aligned}
CI_{i-1} &= init + (i-1) + 1 &&\text{[Hipótese de Indução]} \\
&= init + i &&\text{[Simplificação]} \\
\text{Cycle}([1])_i &= 1 &&\text{[Ciclo Unitário]} \\
CI_i &= CI_{i-1} + \text{Cycle}([1])_i &&\text{[Propriedade do Passo, §3.1]} \\
&= init + i + 1 &&\text{[Substituição]}
\end{aligned}
```

```math
\therefore \ \forall\, i \in \mathbb{N}_0:\ \text{CycleIntegral}([1], init)_i = init + i + 1 \quad \blacksquare\ \text{[C.Q.D.]}
```

Esta propriedade é verificada em [
CycleIntegralOnesProperties::assertCycleIntegralOfOnes
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.17; a prova completa está vinculada na referência ao código-fonte.

**Crescimento estrito.** Para posições $0 \leq a < b$, a forma fechada dá

```math
\begin{aligned}
CI_b - CI_a &= (init + b + 1) - (init + a + 1) &&\text{[Forma Fechada do Ciclo Unitário]} \\
&= b - a &&\text{[Simplificação]} \\
&> 0 &&\text{[Como } b > a\text{]}
\end{aligned}
```

```math
\therefore \ 0 \leq a < b \implies \text{CycleIntegral}([1], init)_b > \text{CycleIntegral}([1], init)_a \quad \blacksquare\ \text{[C.Q.D.]}
```

Esta propriedade é verificada em [
CycleIntegralOnesProperties::assertCycleIntegralOfOnesStrictlyIncreasing
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala). Um trecho central da verificação em Scala está no Apêndice A.17.

## 5. Propriedades Persistentes e Periódicas

Estas propriedades descrevem uma única integral de ciclo fixa: como seus resíduos
se comportam indefinidamente e como ela avança por períodos completos. Todas as seis
propriedades são totalmente verificadas pelo Stainless, exceto as Propriedades 5.3 e 5.4,
que são corolários diretos da Propriedade 5.2.

- Deslocamentos por período de ciclo: um período completo avança a integral pela soma do ciclo — [§5.1](#51-cycle-period-shifts)
- Periodicidade geral de resíduos: qualquer resíduo depende apenas da posição dentro de um período do ciclo — [§5.2](#52-general-residue-periodicity)
- Resíduo não zero persistente: se nenhum resíduo em um período é zero, nenhum jamais será — [§5.3](#53-persistent-non-zero-residue)
- Resíduo zero persistente: se todo resíduo em um período é zero, todo resíduo sempre será — [§5.4](#54-persistent-zero-residue)
- Telescopagem de lacunas: duas lacunas consecutivas somam o intervalo da integral que cobre ambas — [§5.5](#55-gap-telescoping)
- Classificação de resíduos: todos zero, alguns zero, nenhum zero — [§5.6](#56-cycle-residue-classification)

<a id="51-cycle-period-shifts"></a>
### 5.1 Deslocamentos por Período de Ciclo

Após um período completo do ciclo, a integral avança pela soma total do ciclo.
Esse é o limite de terminação para varredura: um sobrevivente é sempre encontrado
dentro de um período do ciclo porque a integral avança por uma quantidade fixa e positiva.

As duas quantidades abaixo pertencem ao ciclo finito de base sobre o qual $ci$
acumula, não ao fluxo de saída do próprio $ci$ — que é ilimitado
e, por [§4.4](#44-cycle-integral-strictly-increasing), estritamente
crescente e nunca se repete:

```math
\begin{aligned}
n &:= \text{period}(ci)
  &&\text{[Comprimento do ciclo finito de base]} \\
\text{periodSum}(ci) &:= \sum_{j=0}^{n-1} \text{cycle}(j)
  &&\text{[Total dos valores de lacuna de um período]}
\end{aligned}
```

```math
\begin{aligned}
\text{ci}(\text{pos} + \text{period}(ci)) &= \text{ci}(\text{pos}) + \text{periodSum}(ci)
  && \text{[Deslocamento por ciclo completo]} \\
\text{ci}(\text{pos} + \text{period}(ci) \cdot m) &= \text{ci}(\text{pos}) + m \cdot \text{periodSum}(ci)
  && \text{[Multi-cycle shift, by induction on } m \text{]}
\end{aligned}
```

**Prova.**

**Passo 0 (identidade base, $pos = 0$).** Ao expandir a definição recursiva
de $ci$ ao longo de um período completo, usando a periodicidade do próprio ciclo
($\text{cycle}(\text{period}(ci)) = \text{cycle}(0)$, pela definição de um
ciclo — [§1](#1-introduction)) e reordenando a soma finita resultante:

```math
\begin{aligned}
ci(\text{period}(ci)) - ci(0)
&= \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1) + \text{cycle}(\text{period}(ci))
  &&\text{[Telescopagem da definição recursiva]} \\
&= \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1) + \text{cycle}(0)
  &&\text{[Periodicidade do ciclo]} \\
&= \text{cycle}(0) + \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1)
  &&\text{[Reordenar termos]} \\
&= \text{periodSum}(ci)
  &&\text{[Pela Definição de periodSum(ci)]}
\end{aligned}
```

```math
\therefore \ ci(\text{period}(ci)) = ci(0) + \text{periodSum}(ci) \quad \blacksquare
```

**Deslocamento por ciclo completo, por indução em $pos$.**

**Caso Base** ($pos = 0$): mostrado no Passo 0.

**Passo de Indução** ($pos > 0$):

```math
\begin{aligned}
ci(\text{pos} - 1 + \text{period}(ci)) &= ci(\text{pos} - 1) + \text{periodSum}(ci)
  &&\text{[Hipótese de Indução]} \\
\text{cycle}(\text{pos} + \text{period}(ci)) &= \text{cycle}(\text{pos})
  &&\text{[Periodicidade do ciclo]} \\
ci(\text{pos} + \text{period}(ci)) &= ci(\text{pos} - 1 + \text{period}(ci)) + \text{cycle}(\text{pos} + \text{period}(ci))
  &&\text{[Pela Definição]} \\
&= \big(ci(\text{pos} - 1) + \text{periodSum}(ci)\big) + \text{cycle}(\text{pos})
  &&\text{[Substituição]} \\
&= \big(ci(\text{pos} - 1) + \text{cycle}(\text{pos})\big) + \text{periodSum}(ci)
  &&\text{[Reagrupamento]} \\
&= ci(\text{pos}) + \text{periodSum}(ci)
  &&\text{[Pela Definição]}
\end{aligned}
```

```math
\therefore \ \forall \ \text{pos} \in \mathbb{N}_0,\ ci(\text{pos} + \text{period}(ci)) = ci(\text{pos}) + \text{periodSum}(ci) \quad \blacksquare
```

**Deslocamento por múltiplos ciclos, por indução em $m$.**

**Caso Base** ($m = 0$):

```math
ci(\text{pos} + \text{period}(ci) \cdot 0) = ci(\text{pos}) = ci(\text{pos}) + 0 \cdot \text{periodSum}(ci)
```

**Passo de Indução** ($m > 0$):

```math
\begin{aligned}
ci(\text{pos} + \text{period}(ci) \cdot (m - 1)) &= ci(\text{pos}) + (m - 1) \cdot \text{periodSum}(ci)
  &&\text{[Hipótese de Indução]} \\
ci\big((\text{pos} + \text{period}(ci) \cdot (m - 1)) + \text{period}(ci)\big) &= ci(\text{pos} + \text{period}(ci) \cdot (m - 1)) + \text{periodSum}(ci)
  &&\text{[Deslocamento por ciclo completo]} \\
ci(\text{pos} + \text{period}(ci) \cdot m) &= \big(ci(\text{pos}) + (m - 1) \cdot \text{periodSum}(ci)\big) + \text{periodSum}(ci)
  &&\text{[Substituição]} \\
&= ci(\text{pos}) + m \cdot \text{periodSum}(ci)
  &&\text{[Aritmética]}
\end{aligned}
```

```math
\therefore \ \forall \ m \in \mathbb{N}_0,\ ci(\text{pos} + \text{period}(ci) \cdot m) = ci(\text{pos}) + m \cdot \text{periodSum}(ci) \quad \blacksquare
```

A identidade de deslocamento por ciclo completo é verificada duas vezes sob nomes diferentes —
[GapProperties::assertPeriodicShift](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)
e `assertFullCycleShift` — ambas invólucros finos sobre o mesmo
lema `CycleIntegralFilterProperties::assertCIShiftEqualsSum`; o artigo
prova a identidade acima uma vez, em vez de duas. A generalização para múltiplos ciclos
é verificada separadamente como `assertMultiCycleShift`. O código central de
verificação em Scala está no Apêndice A.12.

<a id="52-general-residue-periodicity"></a>
### 5.2 Periodicidade Geral de Resíduos

Quando a soma total dos valores de um ciclo é múltipla de `m`, o resíduo
`mod(ci(pos), m)` depende apenas de `pos % ci.period` — ele se repete a cada
período do ciclo. Quando `m` é produto de valores coprimos, o Teorema Chinês
dos Restos [[5]](#ref5) implica que a periodicidade vale simultaneamente para cada fator: o
período do ciclo serve como período comum para todos os resíduos. Essa é a
espinha dorsal aritmética da peneira de Eratóstenes [[5]](#ref5).

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci),\; m) = 0 \;\implies\;
\text{mod}(\text{ci}(\text{pos}),\; m) = \text{mod}(\text{ci}(\text{pos} \bmod \text{period}(ci)),\; m)
\end{aligned}
```

**Prova.** Por indução forte em `pos`, subtraindo um período completo do ciclo por vez.

**Caso Base** $\text{pos} \lt \text{period}(ci)$:

```math
\begin{aligned}
\text{pos} \bmod \text{period}(ci) &= \text{pos}
  &&\text{[Módulo de um valor menor que o divisor]} \\
\text{mod}(ci(\text{pos}), m) &= \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m)
  &&\text{[Substituição]}
\end{aligned}
```

**Passo de Indução** $\text{pos} \geq \text{period}(ci)$: seja $\text{previous} := \text{pos} - \text{period}(ci)$. Pela
identidade de deslocamento por um período provada em [§5.1](#51-cycle-period-shifts),
$ci(\text{previous} + \text{period}(ci)) = ci(\text{previous}) + \text{periodSum}(ci)$, isto é, $ci(\text{pos}) = ci(\text{previous}) + \text{periodSum}(ci)$:

```math
\begin{aligned}
\text{previous} \bmod \text{period}(ci) &= \text{pos} \bmod \text{period}(ci)
  &&\text{[Subtrair um período completo não altera o resíduo da posição]} \\
\text{mod}(ci(\text{previous}), m) &= \text{mod}(ci(\text{previous} \bmod \text{period}(ci)), m)
  &&\text{[Hipótese de Indução]} \\
ci(\text{pos}) &= ci(\text{previous}) + \text{periodSum}(ci)
  &&\text{[Deslocamento por ciclo completo, §5.1]} \\
\text{mod}(ci(\text{pos}), m) &= \text{mod}(ci(\text{previous}) + \text{periodSum}(ci), m)
  &&\text{[Substituição]} \\
&= \text{mod}(ci(\text{previous}), m)
  &&\text{[Since } \text{mod}(\text{periodSum}(ci), m) = 0 \text{]} \\
&= \text{mod}(ci(\text{previous} \bmod \text{period}(ci)), m)
  &&\text{[Pela Hipótese de Indução]} \\
&= \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m)
  &&\text{[Pela igualdade de resíduos acima]}
\end{aligned}
```

```math
\therefore \ \text{mod}(\text{periodSum}(ci), m) = 0 \implies \forall \ \text{pos} \in \mathbb{N}_0,\ \text{mod}(ci(\text{pos}), m) = \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m) \quad \blacksquare\ \text{[C.Q.D.]}
```

Esta propriedade é verificada em [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). O código completo de verificação em Scala está no Apêndice A.11.

A decomposição complementar div/mod `ci(pos) == ci(pos % size) + (pos / size) * ci.sum`
é verificada em `GapProperties::assertCIModDivFormula`.

<a id="53-persistent-non-zero-residue"></a>
### 5.3 Resíduo Não Zero Persistente

Seja $v \in \mathbb{N}$, $v > 0$, com $\text{mod}(\text{periodSum}(ci), v) = 0$. Se
nenhum dos $n$ resíduos em um período completo é zero módulo $v$, então o
resíduo nunca é zero em nenhuma posição, indefinidamente.

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci), v) = 0 \;\land\; \big(\forall\, k \in [0, n),\ \text{mod}(ci(k), v) \neq 0\big)
\implies \forall\, i \in \mathbb{N}_0,\ \text{mod}(ci(i), v) \neq 0
\end{aligned}
```

**Prova.** Por [§5.2](#52-general-residue-periodicity), $\text{mod}(ci(i), v)
= \text{mod}(ci(i \bmod n), v)$ para toda posição $i$. Como $i \bmod n$
sempre cai em $[0, n)$, e nenhum desses $n$ resíduos é zero por
hipótese, o resíduo em qualquer posição $i$ também não pode ser zero.

```math
\begin{aligned}
\text{mod}(ci(i),v) &= \text{mod}(ci(i \bmod n),v) &&\text{[§5.2]} \\
                      &\neq 0 &&\text{[Hipótese dentro do período]} \\
\therefore\ \text{mod}(ci(i),v) &\neq 0.
  \quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Este é um corolário direto do lema de periodicidade [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) usado em [§5.2](#52-general-residue-periodicity); nenhum lema separado é necessário depois que todo resíduo dentro do período é verificado. O código completo de verificação em Scala está no Apêndice A.11.

<a id="54-persistent-zero-residue"></a>
### 5.4 Resíduo Zero Persistente

O caso espelhado: se todo resíduo em um período completo é zero módulo $v$,
então o resíduo permanece zero em toda posição, indefinidamente.

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci), v) = 0 \;\land\; \big(\forall\, k \in [0, n),\ \text{mod}(ci(k), v) = 0\big)
\implies \forall\, i \in \mathbb{N}_0,\ \text{mod}(ci(i), v) = 0
\end{aligned}
```

**Prova.** Idêntica a [§5.3](#53-persistent-non-zero-residue), com a
desigualdade invertida: por [§5.2](#52-general-residue-periodicity),
$\text{mod}(ci(i), v) = \text{mod}(ci(i \bmod n), v)$, e $i \bmod n$
sempre cai entre os $n$ resíduos dentro do período, todos eles zero por
hipótese.

```math
\begin{aligned}
\text{mod}(ci(i),v) &= \text{mod}(ci(i \bmod n),v) &&\text{[§5.2]} \\
                      &= 0 &&\text{[Hipótese dentro do período]} \\
\therefore\ \text{mod}(ci(i),v) &= 0.
  \quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Este é o mesmo corolário de [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) usado em [§5.3](#53-persistent-non-zero-residue), aplicado à hipótese oposta. O código completo de verificação em Scala está no Apêndice A.11.

<a id="55-gap-telescoping"></a>
### 5.5 Telescopagem de Lacunas

Duas lacunas consecutivas telescopam para a diferença da integral ao longo dos dois passos.
Ao aplicar duas vezes o lema de diferença de um passo, os valores das lacunas nas posições
`k` e `k + 1` somam o intervalo da integral de `k - 1` a `k + 1`. Este é
o lema de passo que sustenta a mesclagem de intervalos de lacunas adjacentes.

```math
\begin{aligned}
\text{ci}(k + 1) - \text{ci}(k - 1) = \text{cycle}(k) + \text{cycle}(k + 1)
\quad \text{for } 1 \leq k \text{ and } k + 1 < \text{period}(\text{ci}).
\end{aligned}
```

**Prova.** A propriedade de um passo nas posições $k-1$ e $k$ dá

```math
\begin{aligned}
\text{ci}(k) - \text{ci}(k-1) &= \text{cycle}(k), \\
\text{ci}(k+1) - \text{ci}(k) &= \text{cycle}(k+1).
\end{aligned}
```

Somar essas igualdades cancela $\text{ci}(k)$, então

```math
\begin{aligned}
\therefore\ \text{ci}(k+1) - \text{ci}(k-1)
= \text{cycle}(k) + \text{cycle}(k+1)
\quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertConsecutiveGapSumEqualsDiff
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). O código completo de verificação em Scala está no Apêndice A.10.

<a id="56-cycle-residue-classification"></a>
### 5.6 Classificação de Resíduos do Ciclo

Para qualquer ciclo e módulo `d > 0`, os valores do ciclo caem exatamente
em uma de três categorias de resíduos módulo `d`:

```math
\begin{aligned}
\text{all-zero:} &\quad \forall k,\; \text{mod}(\text{cycle}(k), d) = 0
  && \text{[Filtro remove tudo]} \\
\text{none-zero:} &\quad \forall k,\; \text{mod}(\text{cycle}(k), d) \neq 0
  && \text{[Filtro não tem efeito]} \\
\text{some-zero:} &\quad \exists k_0 : \text{mod}(\text{cycle}(k_0), d) = 0
  \;\land\; \exists k_1 : \text{mod}(\text{cycle}(k_1), d) \neq 0
  && \text{[Filtro remove posições específicas]}
\end{aligned}
```

Esses três estados são detectados por `MemCycle.checkMod(d)` e armazenados em listas
(`modIsZeroForAllValues`, `modIsZeroForNoneValues`, `modIsZeroForSomeValues`).
A avaliação é idempotente — a lista de valores do ciclo nunca muda, apenas os
metadados de classificação são atualizados. Dez lemas em `CycleCheckMod.scala` provam
que a classificação é correta, mutuamente exclusiva e exaustiva.

Essas propriedades são verificadas no módulo [
CycleCheckMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/memory/properties/CycleCheckMod.scala).

## 6. Derivando Novas Integrais de Ciclos

Estas propriedades descrevem como construir uma nova integral de ciclo a partir de uma
integral existente: replicando sua lista de base, deslocando seu índice, rotacionando
suas lacunas, filtrando múltiplos de um valor e reconstruindo diretamente o
resultado filtrado. As Propriedades 6.1 e 6.4–6.10 são totalmente
verificadas pelo Stainless; as Propriedades 6.2 e 6.3 têm provas matemáticas, mas
ainda não foram verificadas pelo Stainless.

- Expansão de ciclo por fator x: o período físico muda enquanto o fluxo representado é preservado — [§6.1](#61-x-fold-cycle-expansion)
- Deslocamentos de índice: à direita e à esquerda — [§6.2](#62-right-index-shift)–[6.3](#63-left-index-shift)
- Rotação de lacunas com ajuste da cabeça: rotacionar o ciclo de lacunas desloca a integral representada em uma posição — [§6.4](#64-gap-rotation-with-head-adjustment)
- Filtragem de sobreviventes: exatidão e estrutura da varredura que retém não múltiplos — [§6.5](#65-survivor-exactness)–[6.6](#66-survivor-structure)
- Reconstrução por filtro e mesclagem: o ciclo de lacunas resultante após remover um múltiplo — [§6.7](#67-merge-shift-law)–[6.10](#610-filtered-result-has-no-multiples)

<a id="61-x-fold-cycle-expansion"></a>
### 6.1 Expansão de Ciclo por Fator x

Seja $L^{(x)}$ a concatenação $x$ vezes de uma lista $L \in 𝕃$. Essa
operação altera o ciclo físico de base, mas não altera o
fluxo ilimitado representado pelo ciclo.

Os valores que mudam são as propriedades finitas de armazenamento:

```math
\begin{aligned}
|L^{(x)}| &= x \cdot |L|
  \quad &&\text{[Período físico expandido]} \\
\sum L^{(x)} &= x \cdot \sum L
  \quad &&\text{[Soma física expandida]}
\end{aligned}
```

A equação do período é verificada em [
RepeatedGapIntegralProperties::assertRepeatedPeriodIsMultiplied
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/RepeatedGapIntegralProperties.scala).

Os valores que não mudam são as propriedades semânticas do fluxo:

```math
\begin{aligned}
L^{(x)}_i &= L_{(i \text{ mod } |L|)}
  \quad &&\text{[Mesma consulta do ciclo]} \\
\text{CycleIntegral}(L^{(x)}, init)_i
  &= \text{CycleIntegral}(L, init)_i
  \quad &&\text{[Mesmo fluxo integral]}
\end{aligned}
```

A equação de consulta do ciclo é verificada em [
RepeatedGapIntegralProperties::assertReplicatedCycleValueEqual
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/RepeatedGapIntegralProperties.scala).

Assim, a expansão não é uma invariância do próprio objeto de ciclo finito. Ela é
uma invariância do fluxo infinito que o objeto de ciclo representa.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}]
  &&\text{[Comprimento do ciclo original]} \\
L^{(x)}
&:= \underbrace{L \mathbin{\texttt{++}} \dots \mathbin{\texttt{++}} L}_{x \text{ copies}}
  &&\text{[Concatenate } x \text{ copies]} \\
m &:= |L^{(x)}| = x \cdot n
  &&\text{[Comprimento do novo ciclo]} \\
T &:= \sum_{j=0}^{n-1} v_j
  &&\text{[Soma do ciclo original]} \\
\end{aligned}
```

A repetição em nível de lista é definida aplicando a lista original no índice original módulo $n$:

```math
\begin{aligned}
L^{(x)}_i &= L_{(i \text{ mod } n)}
  \quad &&\text{for } 0 \le i < x \cdot n \\
\sum L^{(x)} &= x \cdot \sum L
  \quad &&\text{[Soma repetida]}
\end{aligned}
```

Essas propriedades em nível de lista são verificadas por `RepeatedList` e `ListRepeatProperties`: o tamanho da lista repetida é $x \cdot n$, o valor repetido no índice $i$ é o valor original em $i \text{ mod } n$, e a soma repetida é $x$ vezes a soma original. Veja [
RepeatedList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/RepeatedList.scala), [
RepeatedListProperties::assertSumMultiplier
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RepeatedListProperties.scala), and [
ListRepeatProperties::assertRepeatedIndex
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListRepeatProperties.scala).

```math
\begin{aligned}
\text{CycleIntegral}(L^{(x)}, init)_i
&= (i \,\text{div}\, m)\cdot T^{(x)} + I^{(x)}_{i \bmod m} + init
  &&\text{[Pela Definição]} \\
&= (i \,\text{div}\, (x \cdot n))\cdot (x \cdot T) + I^{(x)}_{i \bmod (x \cdot n)} + init
  &&\text{[Substituição]} \\
&= (i \,\text{div}\, n)\cdot T + I_{i \bmod n} + init
  &&\text{[Simplificação exata]} \\
&= \text{CycleIntegral}(L, init)_i
  &&\text{[Reprodução exata do valor]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L^{(x)}, init)_i = \text{CycleIntegral}(L, init)_i \quad \blacksquare
```

Esta propriedade é verificada em [
CycleIntegralProperties::assertRepeatedValuesIntegralMatches
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). O código completo de verificação em Scala está no Apêndice A.8.

<a id="62-right-index-shift"></a>
### 6.2 Deslocamento de Índice à Direita

Seja $L' \in 𝕃$ o deslocamento à direita de $L \in 𝕃$ por uma posição, e seja $init' := init + L_0$ o valor inicial deslocado. Então a CycleIntegral de $L'$ com $init'$ reproduz a CycleIntegral de $L$ com $init$, deslocada em uma posição.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}] \\
L' &:= [v_1, v_2, \dots, v_{n-1}, v_0] \\
S' &= S \quad &\text{[Invariância da Soma do Ciclo]} \\
init' &:= init + L_0 \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_{i+1} &= \text{CycleIntegral}(L', init')_{i} \quad \forall i \in \mathbb{N}_0
\end{aligned}
```

**Caso Base**:

```math
\begin{aligned}
A &:= \text{CycleIntegral}(L, init)_i \\
B &:= \text{CycleIntegral}(L', init')_{i} \\
A_0 &= init + L_0 \\
A_1 &= init + L_0 + L_1 \\
B_0 &= init' + L'_0 = (init + L_0) + L'_0 = init + L_0 + L_1 = A_1 \\
\end{aligned}
```

**Passo de Indução**:

```math
\begin{aligned}
B_{i-1} &= A_i \quad &\text{[Hipótese de Indução]} \\
A_{i+1} &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[Pela Definição]} \\
B_i &= B_{i-1} + L'_{(i \text{ mod } n)} \quad &\text{[Pela Definição]} \\
    &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[Pela Hipótese de Indução]} \\
    &= A_{i+1} \quad &\text{[Pela Definição]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L, init)_{i+1} = \text{CycleIntegral}(L', init')_{i} \quad \blacksquare
```

O invólucro `CycleIntegral` de um período é verificado diretamente. Se o ciclo
deslocado usa a rotação de um passo dos valores originais de base e o valor
inicial deslocado é avançado pela primeira lacuna original, então a integral deslocada
na posição `i` é igual à integral original na posição `i + 1` para todo
índice do período armazenado com `i + 1 < period`.

Esta propriedade é verificada em [
GapProperties::assertRotateOneCycleIntegralShiftsByOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). O código completo de verificação em Scala está no Apêndice A.9.

O enunciado matemático acima é a versão para todas as posições. O
lema verificado prova o núcleo no período armazenado; encapsular a versão universal
para todas as posições só precisa da lei já verificada de deslocamento por ciclo completo.

<a id="63-left-index-shift"></a>
### 6.3 Deslocamento de Índice à Esquerda

Seja $L'' \in 𝕃$ o deslocamento à esquerda de $L \in 𝕃$ por uma posição ($|L| > 1$), e seja $init'' := init + L_0 - L_{n-1}$ o valor inicial deslocado. Então a CycleIntegral de $L''$ com $init''$ reproduz a CycleIntegral de $L$ com $init$, deslocada em uma posição na direção oposta.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}], \quad n > 1 \\
L'' &:= [v_{n-1}, v_0, v_1, \dots, v_{n-2}] \\
S'' &= S \quad &\text{[Invariância da Soma do Ciclo]} \\
init'' &:= init + L_0 - L_{n-1} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &= \text{CycleIntegral}(L'', init'')_{i+1} \quad \forall i \in \mathbb{N}_0
\end{aligned}
```

**Caso Base**:

```math
\begin{aligned}
C &:= \text{CycleIntegral}(L'', init'')_{i} \\
C_1 &= init'' + L''_0 = (init + L_0 - L_{n-1}) + L''_0 \\
    &= init + L_0 - L_{n-1} + L_{n-1} = init + L_0 = A_0 \\
\end{aligned}
```

**Passo de Indução**:

```math
\begin{aligned}
C_{i+1} &= A_i \quad &\text{[Hipótese de Indução]} \\
A_{i+1} &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[Pela Definição]} \\
C_{i+1} &= C_{i} + L''_{(i \text{ mod } n)} \quad &\text{[Pela Definição]} \\
       &= A_i + L_{((i - 1 + n) \text{ mod } n)} \quad &\text{[Pela Hipótese de Indução]} \\
       &= A_{i+1} \quad &\text{[Pela Definição]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L, init)_{i+1} = \text{CycleIntegral}(L'', init'')_{i} \quad \blacksquare
```

<a id="64-gap-rotation-with-head-adjustment"></a>
### 6.4 Rotação de Lacunas com Ajuste da Cabeça

Rotacionar um ciclo de lacunas por uma posição e ajustar a cabeça desloca a
integral inteira em uma posição.

```math
\begin{aligned}
\text{GapList}(\text{head} + \text{gaps}_0,\; \text{tail}(\text{gaps}) \mathbin{\texttt{++}} (\text{gaps}_0 :: L_e))_i
  = \text{GapList}(\text{head},\; \text{gaps})_{i + 1}
  \quad \text{for } 0 \leq i \text{ and } i + 1 < |\text{gaps}|.
\end{aligned}
```

**Prova.** Em $i=0$, a cabeça ajustada é
$\text{head}+\text{gaps}_0$, que é a integral original na posição
$1$. Para $i>0$, suponha que a integral deslocada em $i-1$ seja igual à integral original
em $i$. A lacuna rotacionada em $i$ é a lacuna original em $i+1$;
aplicar a propriedade de um passo às duas integrais dá

```math
\begin{aligned}
I'_i &= I'_{i-1} + \text{gaps}'_{i-1} \\
     &= I_i + \text{gaps}_i \\
     &= I_{i+1}. \\
\therefore\ I'_i &= I_{i+1}
\quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
GapProperties::assertRotateOneShiftsIntegralByOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). Ela delega ao `ShiftedList.assertShiftedApplyIsOriginalPlusOne` verificado; o código-fonte completo está vinculado ali em vez de ser repetido em linha.

Para um valor de filtro $f$ e um intervalo $[start, start + count)$, a sequência de
sobreviventes é a subsequência dos valores de $ci$ nessas posições cujo
resto módulo $f$ é não zero — o análogo, para integrais de ciclos, de um
passo da peneira de Eratóstenes [[5]](#ref5), onde posições divisíveis por $f$ são
removidas e apenas os não múltiplos permanecem:

```math
S := \text{survivorValues}(ci, f, start, count) :=
\big[\, ci(pos) \mid start \le pos < start + count,\ \text{mod}(ci(pos), f) \neq 0 \,\big]
```

Dez lemas verificados em `GapProperties.scala` caracterizam essa sequência.

<a id="65-survivor-exactness"></a>
### 6.5 Exatidão dos Sobreviventes

$S$ é exata por construção: ela é definida exatamente como os não múltiplos de
$f$ no intervalo, nada mais e nada menos. A implementação recursiva em Scala
de `survivorValues` é verificada para calcular exatamente essa especificação.

Isso é verificado em [
GapProperties::assertSurvivorValuesContainsOnlyNonMultiples
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) and [`assertSurvivorValuesContainsNonMultipleAtPosition`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala).

<a id="66-survivor-structure"></a>
### 6.6 Estrutura dos Sobreviventes

Quando todo valor em $[start, pos)$ é múltiplo de $f$ e o próprio $ci(pos)$
não é, $ci(pos)$ é o primeiro sobrevivente, e $S$ se decompõe como esse
valor seguido pelos sobreviventes do restante do intervalo, $(pos, end)$,
onde $end := start + count$:

```math
\begin{aligned}
\big(\forall\, q \in [start, pos),\ \text{mod}(ci(q), f) = 0\big)
  \;\land\; \text{mod}(ci(pos), f) \neq 0
  &\implies \text{head}(S) = ci(pos)
  && \text{[Primeiro sobrevivente]} \\
S &= ci(pos) :: \big[\, ci(q) \mid pos < q < end,\ \text{mod}(ci(q), f) \neq 0 \,\big]
  && \text{[Divisão estrutural]}
\end{aligned}
```

Nas extremidades de um intervalo que também sobrevive, o primeiro e o último
elementos de $S$ são exatamente os valores das extremidades, e ao longo de um período
completo a diferença entre eles é igual à soma total das lacunas do ciclo —
a filtragem não altera quanto a integral avança ao atravessar um período completo:

```math
\begin{aligned}
\text{mod}(ci(start), f) \neq 0
  &\implies \text{head}(S) = ci(start) \\
\text{mod}(ci(start + count - 1), f) \neq 0
  &\implies \text{last}(S) = ci(start + count - 1) \\
\text{mod}(ci(0), f) \neq 0 \;\land\; \text{mod}(ci(n), f) \neq 0
  &\implies \text{last}(S) - \text{head}(S) = \text{periodSum}(ci)
\end{aligned}
```

A lacuna entre dois sobreviventes consecutivos, depois que todo múltiplo intermediário
foi filtrado, é estritamente positiva:

```math
\text{mod}(ci(from), f) \neq 0 \;\land\; \text{mod}(ci(to), f) \neq 0
\;\land\; \big(\forall\, q \in (from, to),\ \text{mod}(ci(q), f) = 0\big)
\implies ci(to) - ci(from) > 0
```

Todas as propriedades de estrutura dos sobreviventes são verificadas em [
GapProperties::assertFirstSurvivorAtPosition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertSurvivorValuesSplitAtFirstPosition`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertFirstSurvivorIsHead`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertLastSurvivorIsLastScanned`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertFilteredSumEqualsOriginalSum`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), and [`assertMergedGapPositive`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala).

A filtragem remove um valor; os valores sobreviventes ainda devem formar uma lista válida
de lacunas de integral de ciclo. Esta seção prova que remover um múltiplo por meio da
mesclagem de suas duas lacunas vizinhas produz exatamente a integral de ciclo que
uma construção nova a partir da lista de sobreviventes produziria, e que o
resultado não contém múltiplos do valor de filtro em nenhuma posição.

<a id="67-merge-shift-law"></a>
### 6.7 Lei de Deslocamento por Mesclagem

Seja $ci$ uma integral de ciclo com período $n$, e seja $m$ um índice de mesclagem
com $0 \le m$ e $m + 1 < n$. Seja $ci'$ uma integral de ciclo com período
$n - 1$, o mesmo valor inicial e um ciclo de lacunas igual ao de $ci$, exceto
que as lacunas em $m$ e $m + 1$ são combinadas em uma:

```math
\begin{aligned}
\text{cycle}'(i) &= \text{cycle}(i)
  &&\text{for } i < m \\
\text{cycle}'(m) &= \text{cycle}(m) + \text{cycle}(m + 1) \\
\text{cycle}'(i) &= \text{cycle}(i + 1)
  &&\text{for } i > m
\end{aligned}
```

Então $ci'$ coincide com $ci$ antes do ponto de mesclagem, e coincide com $ci$
uma posição à frente no ponto de mesclagem e depois dele:

```math
\begin{aligned}
pos < m &\implies ci'(pos) = ci(pos)
  &&\text{[Antes da mesclagem]} \\
ci'(m) &= ci(m + 1)
  &&\text{[Na mesclagem]} \\
pos > m &\implies ci'(pos) = ci(pos + 1)
  &&\text{[Após a mesclagem]} \\
ci'(n - 1) &= ci(n)
  &&\text{[Fronteira do período]}
\end{aligned}
```

**Prova.** Por indução na posição, usando a propriedade do passo
([§3.1](#31-recursive-cycle-integral)) em cada um dos três casos divididos no
ponto de mesclagem.

**Caso 1: Antes da mesclagem** ($pos < m$), por indução em $pos$.

**Caso Base** ($pos = 0$):

```math
\begin{aligned}
ci'(0) &= init + \text{cycle}'(0)
  &&\text{[Pela Definição]} \\
&= init + \text{cycle}(0)
  &&\text{[Mesmo valor inicial; lacuna antes da mesclagem inalterada]} \\
&= ci(0)
  &&\text{[Pela Definição]}
\end{aligned}
```

**Passo de Indução** ($0 < pos < m$):

```math
\begin{aligned}
ci'(pos - 1) &= ci(pos - 1)
  &&\text{[Hipótese de Indução]} \\
ci'(pos) &= ci'(pos - 1) + \text{cycle}'(pos)
  &&\text{[Pela Definição]} \\
&= ci(pos - 1) + \text{cycle}(pos)
  &&\text{[Substituição; lacuna antes da mesclagem inalterada]} \\
&= ci(pos)
  &&\text{[Pela Definição]}
\end{aligned}
```

```math
\therefore \ pos < m \implies ci'(pos) = ci(pos) \quad \blacksquare
```

**Caso 2: No ponto de mesclagem** ($pos = m$). Para $m > 0$, usando o Caso 1 em $m - 1$:

```math
\begin{aligned}
ci'(m) &= ci'(m - 1) + \text{cycle}'(m)
  &&\text{[Pela Definição]} \\
&= ci(m - 1) + \big(\text{cycle}(m) + \text{cycle}(m + 1)\big)
  &&\text{[Caso 1; definição da lacuna mesclada]} \\
&= \big(ci(m - 1) + \text{cycle}(m)\big) + \text{cycle}(m + 1)
  &&\text{[Reagrupamento]} \\
&= ci(m) + \text{cycle}(m + 1)
  &&\text{[Pela Definição]} \\
&= ci(m + 1)
  &&\text{[Pela Definição]}
\end{aligned}
```

Para $m = 0$, a mesma identidade vale diretamente, sem depender do Caso 1:
$ci'(0) = init + \text{cycle}'(0) = init + \text{cycle}(0) + \text{cycle}(1) = ci(1)$.

```math
\therefore \ ci'(m) = ci(m + 1) \quad \blacksquare
```

**Caso 3: Depois da mesclagem** ($pos > m$), por indução em $pos$.

**Caso Base** ($pos = m + 1$), usando o Caso 2:

```math
\begin{aligned}
ci'(m + 1) &= ci'(m) + \text{cycle}'(m + 1)
  &&\text{[Pela Definição]} \\
&= ci(m + 1) + \text{cycle}(m + 2)
  &&\text{[Caso 2; definição da lacuna deslocada]} \\
&= ci(m + 2)
  &&\text{[Pela Definição]}
\end{aligned}
```

**Passo de Indução** ($pos > m + 1$):

```math
\begin{aligned}
ci'(pos - 1) &= ci(pos)
  &&\text{[Hipótese de Indução]} \\
ci'(pos) &= ci'(pos - 1) + \text{cycle}'(pos)
  &&\text{[Pela Definição]} \\
&= ci(pos) + \text{cycle}(pos + 1)
  &&\text{[Substituição; definição da lacuna deslocada]} \\
&= ci(pos + 1)
  &&\text{[Pela Definição]}
\end{aligned}
```

```math
\therefore \ pos > m \implies ci'(pos) = ci(pos + 1) \quad \blacksquare
```

O caso da fronteira do período é a última instância do Caso 3, em $pos = n - 1$:
$ci'(n - 1) = ci(n)$.

Esta propriedade é verificada em [
CycleIntegralFilterProperties::assertSameBeforeMerge
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertShiftAtMerge`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertShiftAfterMerge`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), e [`assertNewCIAtSizeEqualsOld`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). O código completo de verificação em Scala está no Apêndice A.13.

<a id="68-removing-a-multiple"></a>
### 6.8 Removendo um Múltiplo

Quando o valor no ponto de mesclagem é múltiplo de um valor de filtro $f$,
mesclar suas duas lacunas vizinhas o remove completamente da sequência:
o valor da nova integral nessa posição é o próximo valor da integral antiga,
que por construção não é ele próprio um múltiplo.

```math
\begin{aligned}
\text{mod}(ci(0), f) \neq 0 \;\land\; \text{mod}(ci(m), f) = 0
&\implies ci'(m) = ci(m + 1)
&&\text{[Múltiplo removido]} \\
\text{mod}(ci(m + 1), f) \neq 0
&\implies \text{mod}(ci'(m), f) \neq 0
&&\text{[Resultado não é múltiplo]}
\end{aligned}
```

**Prova.** A primeira identidade é o caso "no ponto de mesclagem" da lei de deslocamento por mesclagem
([§6.7](#67-merge-shift-law)) aplicado diretamente: $ci'(m) = ci(m + 1)$
independentemente de $ci(m)$ ser múltiplo. A segunda segue porque
valores iguais satisfazem a mesma condição modular.

Esta propriedade é verificada em [
CycleIntegralFilterProperties::assertRemoveOneMultiple
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala) e [`assertRemoveMultipleModNotZero`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). O código completo de verificação em Scala está no Apêndice A.14.

<a id="69-direct-construction-from-survivors"></a>
### 6.9 Construção Direta a partir dos Sobreviventes

Em vez de mesclar lacunas um múltiplo por vez, uma integral de ciclo filtrada
pode ser construída diretamente a partir da lista de sobreviventes ([§6.5](#65-survivor-exactness)):
seu valor inicial é o primeiro sobrevivente, e seu ciclo de lacunas é a lista das
diferenças entre sobreviventes consecutivos. Essa construção direta
reproduz exatamente o que a mesclagem repetida produziria.

```math
\begin{aligned}
S &:= \text{survivorValues}(ci, f, 0, n) \\
ci''\text{'s initial value} &= S_0,\quad \text{cycle}''(i) = S_{i+1} - S_i \\
\implies ci''(k) &= S_{k + 1}
&&\text{[Construção direta coincide com sobreviventes]}
\end{aligned}
```

**Prova.** Por indução em $k$. O caso base segue diretamente da
própria definição da integral aplicada à primeira lacuna. O passo indutivo
adiciona a $k$-ésima lacuna construída, que por definição é igual a
$S_{k+1} - S_k$, à hipótese de indução $ci''(k-1) = S_k$, obtendo
$ci''(k) = S_{k+1}$.

Esta propriedade é verificada em [
CycleIntegralFilterProperties::assertNewCIGeneratesFiltered
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertNewCIMatchesSurvivors`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), e [`assertGapsFromSurvivorsMatchCI`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). O código completo de verificação em Scala está no Apêndice A.15.

<a id="610-filtered-result-has-no-multiples"></a>
### 6.10 Resultado Filtrado Não Tem Múltiplos

A integral de ciclo construída diretamente a partir da lista de sobreviventes não contém
múltiplos do valor de filtro em nenhuma posição — seus valores são, por
construção, exatamente os sobreviventes.

```math
\begin{aligned}
\text{mod}(ci(0), f) \neq 0 \implies
\text{mod}(ci''(k), f) \neq 0
\quad \text{for every valid } k
\end{aligned}
```

**Prova.** Por [§6.9](#69-direct-construction-from-survivors), $ci''(k)$
é igual ao sobrevivente $S_{k+1}$, e já se sabe que todo elemento da lista de sobreviventes
não é múltiplo de $f$
([§6.5](#65-survivor-exactness)).

```math
\begin{aligned}
ci''(k) &= S_{k+1} &&\text{[§6.9]} \\
\text{mod}(S_{k+1},f) &\neq 0 &&\text{[§6.5]} \\
\therefore\ \text{mod}(ci''(k),f) &\neq 0.
  \quad \blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
CycleIntegralFilterProperties::assertFilterMergeComposition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala) e [`assertNextGapsValid`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). O código completo de verificação em Scala está no Apêndice A.16.

## 7. Conclusão

Este artigo estende os fundamentos previamente verificados para listas recursivas,
integrais discretas, aritmética modular e ciclos, a fim de definir e raciocinar sobre
Integrais de Ciclos. Partindo de uma lista finita não vazia, a construção trata
a lista como um ciclo repetitivo e descreve o valor acumulado em qualquer
índice não negativo usando a soma do ciclo, a posição modular e o valor inicial.

Definimos duas apresentações equivalentes de Integral de Ciclo: **CycleIntegral**,
uma acumulação recursiva sobre um ciclo apoiado em memória ([§3.1](#31-recursive-cycle-integral)),
e **ModCycleIntegral**, uma definição em forma fechada usando divisão e módulo
([§3.2](#32-modulo-cycle-integral)).

Para ambas as apresentações, verificamos a propriedade da soma (a integral é igual à soma cumulativa do ciclo) e a propriedade do passo (a diferença entre valores consecutivos é igual ao elemento correspondente do ciclo). Também provamos a equivalência entre as definições recursiva e modular, que a integral é estritamente crescente sob valores-base positivos, e que ela permanece positiva em toda posição dado um início não negativo. O bloco central se encerra com sua instância mais simples: o ciclo unitário $[1]$, cuja integral enumera os inteiros consecutivos $init + i + 1$ em ordem estritamente crescente — o fluxo de candidatos que os artigos sobre sequências de peneira filtram depois.

Além dessas definições centrais, o artigo verifica várias leis reutilizáveis
de integrais de ciclos. Dentro de uma integral de ciclo fixa: os resíduos são periódicos
quando a soma do ciclo é zero módulo o módulo escolhido, com os casos persistentes
de não zero e de zero seguindo como corolários imediatos;
lacunas adjacentes telescopam em diferenças da integral; deslocamentos por ciclo completo avançam
a integral pela soma do ciclo; e a classificação de resíduos do ciclo é correta,
exclusiva e exaustiva. Ao construir novas integrais de ciclos a partir de existentes:
repetir um ciclo de base preserva o fluxo integral representado;
rotacionar um ciclo de lacunas com o ajuste correspondente da cabeça desloca a
integral representada em uma posição; varreduras de sobreviventes retêm exatamente os
não múltiplos necessários para a filtragem; e mesclar as duas lacunas ao redor de um
múltiplo removido reconstrói exatamente a integral de ciclo que uma construção nova
a partir da lista de sobreviventes produziria, sem que sobrem múltiplos do
valor de filtro em qualquer ponto do resultado. Os pontos abertos de extensão
são as leis de deslocamento de índice nas Seções 6.2 e 6.3.

As principais propriedades estabelecidas são:

```math
\begin{aligned}
&\forall \ L \in 𝕃,\quad \forall \ init \in \mathbb{N}_0,\quad \forall \ i \in \mathbb{N}_0 \\
L &= [v_0, v_1, \dots, v_{n-1}], \quad n = |L|,\quad n > 0 \\
T &= \sum_{j=0}^{n-1} v_j \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i
&= \left(i \ \text{div}\ n\right) \cdot T
 + \text{CycleIntegral}(L, init)_{i \text{mod} n}
\quad &\text{[Integral de Ciclo Modular]} \\
\text{CycleIntegral}(L, init)_i
&= \text{ModCycleIntegral}(L, init)_i
\quad &\text{[Equivalência das Definições]} \\
\text{CycleIntegral}(L, init)_{i+1}
&- \text{CycleIntegral}(L, init)_i
= \text{Cycle}(L)_{i+1}
\quad &\text{[Propriedade do Passo]} \\
\text{CycleIntegral}(L, init)_{i+1}
&- \text{CycleIntegral}(L, init)_i \\
&= \text{CycleIntegral}(L, init)_{i+n+1}
 - \text{CycleIntegral}(L, init)_{i+n}
\quad &\text{[Mesma Diferença Após Ciclo Completo]} \\
\text{CycleIntegral}(L, init)_i
&= \text{sum}([init] \mathbin{\texttt{++}}
 [\text{Cycle}(L)_0, \ldots, \text{Cycle}(L)_i])
\quad &\text{[Soma de Valores Modulares como Lista]} \\
init \geq 0 \land (\forall x \in L,\ x > 0) \land b > a
&\implies
\text{CycleIntegral}(L, init)_b > \text{CycleIntegral}(L, init)_a
\quad &\text{[Estritamente Crescente]} \\
init \geq 0 \land (\forall x \in L,\ x > 0)
&\implies
\text{CycleIntegral}(L, init)_i > 0
\quad &\text{[Positividade]} \\
\text{CycleIntegral}([1], init)_i
&= init + i + 1
\quad &\text{[Geração pelo Ciclo Unitário]} \\
0 \leq a < b \implies
\text{CycleIntegral}([1], init)_b
&> \text{CycleIntegral}([1], init)_a
\quad &\text{[Crescimento Estrito do Ciclo Unitário]} \\
\end{aligned}
```

```math
\begin{aligned}
ci(pos + \text{period}(ci))
&= ci(pos) + \text{periodSum}(ci)
\quad &\text{[Deslocamento por Período de Ciclo]} \\
\text{mod}(\text{periodSum}(ci), m) = 0
&\implies
\text{mod}(ci(pos), m) = \text{mod}(ci(pos \bmod n), m)
\quad &\text{[Periodicidade Geral de Resíduos]} \\
\text{mod}(\text{periodSum}(ci), m) = 0 \land \big(\forall\, k \in [0,n),\ \text{mod}(ci(k), m) \neq 0\big)
&\implies
\forall\, i,\ \text{mod}(ci(i), m) \neq 0
\quad &\text{[Resíduo Não Zero Persistente]} \\
\text{mod}(\text{periodSum}(ci), m) = 0 \land \big(\forall\, k \in [0,n),\ \text{mod}(ci(k), m) = 0\big)
&\implies
\forall\, i,\ \text{mod}(ci(i), m) = 0
\quad &\text{[Resíduo Zero Persistente]} \\
\text{CycleIntegral}(G,h)_{k+1}
&- \text{CycleIntegral}(G,h)_{k-1}
= G_{k-1} + G_k
\quad &\text{[Telescopagem de Duas Lacunas]} \\
\text{classify}(I_i,m)
&\in \{\text{zero},\text{nonzero}\}
\quad &\text{[Classificação de Resíduos]} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L^{\langle x\rangle}, init)_i
&= \text{CycleIntegral}(L, init)_i
\quad &\text{[Invariância por Ciclo Repetido]} \\
\text{rotateAt}(G,1)\text{ with head }h+G_0
&\implies
I'_{i}=I_{i+1}
\quad &\text{[Deslocamento por Rotação]} \\
\text{survivors}(I,m)
&= \{ I_i \mid I_i \not\equiv 0 \pmod m \}
\quad &\text{[Exatidão dos Sobreviventes]} \\
\big(\forall\, q \in [start,pos),\ \text{mod}(ci(q),f)=0\big) \land \text{mod}(ci(pos),f)\neq 0
&\implies
\text{head}(S) = ci(pos)
\quad &\text{[Estrutura dos Sobreviventes]} \\
\end{aligned}
```

```math
\begin{aligned}
ci'(m) &= ci(m + 1)
\quad &\text{[Lei de Deslocamento por Mesclagem]} \\
\text{mod}(ci(m), f) = 0 \implies ci'(m) &= ci(m + 1)
\quad &\text{[Removendo um Múltiplo]} \\
ci''\text{'s initial value} = S_0 \land \text{cycle}''(i) = S_{i+1} - S_i
&\implies ci''(k) = S_{k+1}
\quad &\text{[Construção Direta a partir dos Sobreviventes]} \\
\text{mod}(ci(0), f) \neq 0 &\implies \text{mod}(ci''(k), f) \neq 0
\quad &\text{[Resultado Filtrado Não Tem Múltiplos]} \\
\end{aligned}
```

As definições verificadas fornecem uma base reutilizável para raciocinar sobre acumulações periódicas
infinitas usando estruturas finitas de listas e código Scala verificado por máquina.

## 8. Trabalhos Futuros

A continuação mais próxima é fechar as propriedades restantes de deslocamento de índice na
Seção 6. Esses enunciados já têm derivações matemáticas no
artigo, mas ainda ficam na fronteira entre a biblioteca verificada de integrais de ciclos
e o raciocínio mais forte sobre deslocamentos necessário para argumentos posteriores da peneira.

Depois disso, a mesma maquinaria de período finito pode sustentar propriedades mais especializadas
da peneira de primos: detectar resíduos aceitos, acompanhar a evolução das lacunas
através dos filtros e relacionar janelas locais de sobreviventes à estrutura de
ciclos completos. Extensões mais distantes, como ciclos multidimensionais ou
integração sobre estruturas algébricas mais ricas, exigiriam novas definições
em vez de uma continuação direta da prova presente.

## Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). _Using Formal Verification to Prove Properties of Lists Recursively Defined_. Disponível em: [https://rxiverse.org/abs/2609.0023](https://rxiverse.org/abs/2609.0023)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). _Formal Verification of Discrete Integration Properties from First Principles_. Disponível em: [https://doi.org/10.5281/zenodo.22746792](https://doi.org/10.5281/zenodo.22746792)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). _Formal Verification of Cyclic Lists_. Disponível em: [https://doi.org/10.5281/zenodo.22865441](https://doi.org/10.5281/zenodo.22865441)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). _Division and Modulo from Recursive Normalization_. Disponível em: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. & Wright, E. M. (1979). _An Introduction to the Theory of Numbers_ (5th ed.). Oxford University Press. §5.4 (Chinese Remainder Theorem), §15.1 (Sieve of Eratosthenes).

<a name="ref6" id="ref6" href="#ref6">[6]</a>
The Lean Community. *Mathlib: Periodic Functions*.
Disponível em: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Periodic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Periodic.html)

<a name="ref7" id="ref7" href="#ref7">[7]</a>
The Lean Community. *Mathlib: Cycles of Lists*.
Disponível em: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Cycle.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Cycle.html)

## Apêndice A: Código de Verificação em Scala

### A.1 Propriedade da Soma para Posições Pequenas — assertCycleIntegralEqualsSumSmallPositions

Fonte: [CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertCycleIntegralEqualsSumSmallPositions(
  cycleIntegral: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position < cycleIntegral.period)
  require(position > 0)
  require(ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position - 1)) == cycleIntegral(position - 1))

  assert(assertNextPosition(cycleIntegral, position))
  assert(cycleIntegral(position) ==
    cycleIntegral.cycle(position) + cycleIntegral(position - 1))
  assert(MemCycleProperties.smallValueInCycle(
    cycleIntegral.cycle, position))
  assert(cycleIntegral.cycle(position) ==
    cycleIntegral.cycle.values(position))
  assert(ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position - 1)) == cycleIntegral(position - 1))

  val prev = getFirstValuesAsSlice(cycleIntegral, position - 1)
  val prevSum = ListUtils.sum(prev)
  assert(prevSum == cycleIntegral(position - 1))

  val currentList = List(cycleIntegral.cycle.values(position)) ++ prev
  val currentValue = cycleIntegral.cycle(position)
  val currentSum = ListUtils.sum(prev) + currentValue
  assert(ListUtilsProperties.listAddValueTail(prev, currentValue))
  assert(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
  assert(assertNextPosition(
    cycleIntegral = cycleIntegral, position = position))

  ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position)) == cycleIntegral(position)
}.holds
```

### A.2 Propriedade do Passo — assertDiffEqualsCycleValue

Fonte: [CycleIntegralProperties::assertDiffEqualsCycleValue](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertDiffEqualsCycleValue(
  cycleIntegral: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  assert(cycleIntegral(position + 1) ==
    cycleIntegral(position) + cycleIntegral.cycle(position + 1))
  cycleIntegral(position + 1) - cycleIntegral(position) ==
    cycleIntegral.cycle(position + 1)
}.holds
```

### A.3 Primeiros Valores Modulares Coincidem com a Integral — assertFirstValuesMatchIntegral

Fonte: [ModCycleIntegralProperties::assertFirstValuesMatchIntegral](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertFirstValuesMatchIntegral(
  modCycleIntegral: ModCycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  require(position < modCycleIntegral.integralValues.size)
  assert(ModSmallDividend.modSmallDividend(
    position, modCycleIntegral.integralValues.size))
  assert(Calc.mod(
    position, modCycleIntegral.integralValues.size) == position)
  assert(Calc.div(
    position, modCycleIntegral.integralValues.size) == 0)

  modCycleIntegral.apply(position) ==
    modCycleIntegral.integralValues(position) + modCycleIntegral.initialValue
}.holds
```

### A.4 Diferença do Passo Modular — assertSimplifiedDiffValuesMatchCycle

Fonte: [ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertSimplifiedDiffValuesMatchCycle(
  modCycleIntegral: ModCycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  assert(modCycleIntegral.integralValues.size ==
    modCycleIntegral.mCycle.size)
  ModOperations.addOne(
    position, modCycleIntegral.integralValues.size)

  if (Calc.mod(position, modCycleIntegral.integralValues.size) ==
      modCycleIntegral.integralValues.size - 1) {
    // ... boundary case: position mod size == size - 1
    // (full proof omitted for brevity — see source file)
  } else {
    // ... non-boundary case
    // (full proof omitted for brevity — see source file)
  }

  modCycleIntegral.apply(position + 1) -
    modCycleIntegral.apply(position) ==
    modCycleIntegral.mCycle.values(
      Calc.mod(position + 1, modCycleIntegral.integralValues.size))
}.holds
```

### A.5 Equivalência das Definições — assertCycleIntegralMatchModCycleDef

Fonte: [ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertCycleIntegralMatchModCycleDef(
  modCycleIntegral: ModCycleIntegral,
  cycleIntegral: CycleIntegral,
  position: BigInt,
): Boolean = {
  require(position >= 0)
  require(modCycleIntegral.mCycle.values.nonEmpty)
  require(cycleIntegral.cycle.values.nonEmpty)
  require(modCycleIntegral.mCycle.values == cycleIntegral.cycle.values)
  require(modCycleIntegral.mCycle.size == cycleIntegral.cycle.size)
  require(modCycleIntegral.initialValue == cycleIntegral.initialValue)
  decreases(position)

  assertModCycleEqualsCycleIntegral(
    modCycleIntegral, cycleIntegral, position)
  val size = modCycleIntegral.mCycle.size

  assert(modCycleIntegral(position) == cycleIntegral(position))
  assert(
    modCycleIntegral(position) ==
      div(position, size) * modCycleIntegral.integralValues.last +
      modCycleIntegral.integralValues(mod(position, size)) +
      modCycleIntegral.initialValue
  )

  cycleIntegral(position) ==
    div(position, size) * modCycleIntegral.integralValues.last +
    modCycleIntegral.integralValues(mod(position, size)) +
    cycleIntegral.initialValue
}.holds
```

### A.6 Mesma Diferença Após Ciclo Completo — assertSameDiffAfterCycle

Fonte: [CycleIntegralProperties::assertSameDiffAfterCycle](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertSameDiffAfterCycle(
  iCycle: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)

  val a = position
  val b = position + 1
  val c = a + iCycle.size
  val d = b + iCycle.size

  assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = a)
  assert(iCycle(b) - iCycle(a) == iCycle.cycle(b))

  assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = c)
  assert(iCycle(d) - iCycle(c) == iCycle.cycle(d))

  MemCycleProperties.valueMatchAfterManyLoopsInBoth(
    iCycle.cycle, a, 0, 1)
  MemCycleProperties.valueMatchAfterManyLoopsInBoth(
    iCycle.cycle, b, 0, 1)

  assert(iCycle.cycle(d) == iCycle.cycle(b))
  assert(iCycle.cycle(c) == iCycle.cycle(a))

  iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
}.holds
```

### A.7 Soma de Valores Modulares como Lista — assertSumModValueAsListEqualsCycleIntegralLoop

Fonte: [CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertSumModValueAsListEqualsCycleIntegralLoop(
  iCycle: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  decreases(position)

  if (position == 0) {
    assert(iCycle(position) ==
      ListUtils.sum(getModValuesAsList(iCycle, position)))
    iCycle(position) == iCycle.cycle(0) + iCycle.initialValue &&
      iCycle(position) ==
        ListUtils.sum(getModValuesAsList(iCycle, position))
  } else {
    if (position > iCycle.size) {
      assertSameDiffAfterCycle(iCycle, position - iCycle.size)
      // ... inductive step details
    }
    assertSumModValueAsListEqualsCycleIntegralLoop(
      iCycle, position - 1)
    assert(iCycle(position - 1) ==
      ListUtils.sum(getModValuesAsList(iCycle, position - 1)))
    assert(ListUtilsProperties.listAddValueTail(
      getModValuesAsList(iCycle, position - 1), iCycle.cycle(position)))
    iCycle(position) == iCycle.cycle(position) + iCycle(position - 1) &&
      iCycle(position) ==
        ListUtils.sum(getModValuesAsList(iCycle, position))
  }
}.holds
```

### A.8 Expansão de Ciclo por Fator x — assertRepeatedValuesIntegralMatches

Fonte: [CycleIntegralProperties::assertRepeatedValuesIntegralMatches](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertRepeatedValuesIntegralMatches(
  cycleIntegral: CycleIntegral,
  repeatedCycleIntegral: CycleIntegral,
  times: BigInt,
  position: BigInt
): Boolean = {
  require(times > BigInt(0))
  require(position >= BigInt(0))
  require(cycleIntegral.cycle.period > BigInt(0))
  require(repeatedCycleIntegral.initialValue == cycleIntegral.initialValue)
  require(repeatedCycleIntegral.cycle.values ==
    ListRepeatProperties.repeat(cycleIntegral.cycle.values, times))
  RepeatedGapIntegralProperties.assertRepeatedValuesIntegralMatches(
    cycleIntegral, repeatedCycleIntegral, times, position
  )
}.holds
```

### A.9 Núcleo do Deslocamento de Índice à Direita — assertRotateOneCycleIntegralShiftsByOne

Fonte: [GapProperties::assertRotateOneCycleIntegralShiftsByOne](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertRotateOneCycleIntegralShiftsByOne(
  originalCI: CycleIntegral,
  shiftedCI: CycleIntegral,
  i: BigInt
): Boolean = {
  require(i >= 0)
  require(i + 1 < originalCI.period)
  require(shiftedCI.initialValue == originalCI.initialValue + originalCI.cycle(0))
  require(shiftedCI.cycle.values == ListUtils.rotateAt(originalCI.cycle.values, BigInt(1)))
  decreases(i)

  assert(originalCI.cycle.values.nonEmpty)
  assert(RotationProperties.assertRotateSameSize(originalCI.cycle.values, BigInt(1)))
  assert(shiftedCI.period == originalCI.period)
  assert(RotationProperties.assertRotatedAtIndexPlusOne(originalCI.cycle.values, i))
  assert(shiftedCI.cycle(i) == originalCI.cycle(i + 1))

  if (i == BigInt(0)) {
    assert(shiftedCI(i) == shiftedCI.initialValue + shiftedCI.cycle(0))
    assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
    assert(originalCI(i) == originalCI.initialValue + originalCI.cycle(0))
    assert(shiftedCI(i) == originalCI(i + 1))
  } else {
    assert(assertRotateOneCycleIntegralShiftsByOne(originalCI, shiftedCI, i - BigInt(1)))
    assert(shiftedCI(i - BigInt(1)) == originalCI(i))
    assert(shiftedCI(i) == shiftedCI(i - BigInt(1)) + shiftedCI.cycle(i))
    assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
    assert(shiftedCI(i) == originalCI(i + 1))
  }

  shiftedCI(i) == originalCI(i + 1)
}.holds
```

### A.10 Telescopagem de Lacunas — assertConsecutiveGapSumEqualsDiff

Fonte: [CycleIntegralProperties::assertConsecutiveGapSumEqualsDiff](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertConsecutiveGapSumEqualsDiff(
  ci: CycleIntegral,
  k: BigInt
): Boolean = {
  require(k >= BigInt(1))
  require(ci.cycle.period > k + BigInt(1))
  require(ci.cycle.values.nonEmpty)

  assert(assertDiffEqualsCycleValue(ci, k - BigInt(1)))
  assert(assertDiffEqualsCycleValue(ci, k))

  ci(k + BigInt(1)) - ci(k - BigInt(1)) ==
    ci.cycle(k) + ci.cycle(k + BigInt(1))
}.holds
```

### A.11 Periodicidade Modular — assertModIsPeriodic

Fonte: [GapProperties::assertModIsPeriodic](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertModIsPeriodic(
  ci: CycleIntegral,
  m: BigInt,
  pos: BigInt
): Boolean = {
  require(ci.period > 0)
  require(m > 0)
  require(pos >= 0)
  require(Calc.mod(ci.sum, m) == BigInt(0))
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  decreases(pos)

  val size = ci.period
  val r = Calc.mod(pos, size)

  if (pos < size) {
    assert(ModSmallDividend.modSmallDividend(pos, size))
    assert(r == pos)
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
  } else {
    val previous = pos - size
    val previousR = Calc.mod(previous, size)

    assert(previous >= BigInt(0))
    assert(previous < pos)
    assert(previous + size == pos)
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(previous, size))
    assert(Calc.mod(previous + size, size) == Calc.mod(previous, size))
    assert(r == previousR)

    assert(assertModIsPeriodic(ci, m, previous))
    assert(Calc.mod(ci(previous), m) == Calc.mod(ci(previousR), m))

    assert(CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, previous))
    assert(ci(previous + size) - ci(previous) == ci.sum)
    assert(ci(pos) - ci(previous) == ci.sum)
    assert(ci(pos) == ci(previous) + ci.sum)

    assert(assertAddZeroModValuePreservesMod(ci(previous), ci.sum, m))
    assert(Calc.mod(ci(previous) + ci.sum, m) == Calc.mod(ci(previous), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previous), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previousR), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
  }

  Calc.mod(ci(pos), m) == Calc.mod(ci(r), m)
}.holds
```

### A.12 Deslocamentos por Período de Ciclo — assertPeriodicShift, assertFullCycleShift, assertMultiCycleShift

Fonte: [lemas de deslocamento por período de ciclo em GapProperties](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertPeriodicShift(
  ci: CycleIntegral,
  k: BigInt
): Boolean = {
  require(ci.period > 0)
  require(k >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, k)
}.holds

def assertFullCycleShift(
  ci: CycleIntegral,
  pos: BigInt
): Boolean = {
  require(ci.period > 0)
  require(pos >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, pos)
}.holds

def assertMultiCycleShift(
  ci: CycleIntegral,
  pos: BigInt,
  m: BigInt
): Boolean = {
  require(ci.period > 0)
  require(pos >= 0)
  require(m >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  decreases(m)

  val period = ci.period
  val totalGaps = ci.sum

  if (m == BigInt(0)) {
    ci(pos) == ci(pos) + totalGaps * BigInt(0)
  } else {
    assert(assertFullCycleShift(ci, pos + period * (m - BigInt(1))))
    assert(ci(pos + period * (m - BigInt(1)) + period) ==
      ci(pos + period * (m - BigInt(1))) + totalGaps)

    assert(assertMultiCycleShift(ci, pos, m - BigInt(1)))
    assert(ci(pos + period * (m - BigInt(1))) ==
      ci(pos) + totalGaps * (m - BigInt(1)))

    ci(pos + period * m) == ci(pos) + totalGaps * m
  }
}.holds
```

### A.13 Lei de Deslocamento por Mesclagem — assertShiftAtMerge

Fonte: [CycleIntegralFilterProperties::assertShiftAtMerge](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertShiftAtMerge(
  oldIntegral: CycleIntegral,
  newIntegral: CycleIntegral,
  mergeIndex: BigInt
): Boolean = {
  require(mergeIndex >= 0)
  require(mergeIndex + 1 < oldIntegral.period)
  require(newIntegral.period == oldIntegral.period - 1)
  require(oldIntegral.initialValue == newIntegral.initialValue)
  require(newIntegral.cycle(mergeIndex) ==
    oldIntegral.cycle(mergeIndex) +
      oldIntegral.cycle(mergeIndex + 1))
  require(allGapsMatchBeforeMerge(
    oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
  if (mergeIndex == 0) {
    assert(newIntegral(0) ==
      newIntegral.initialValue + newIntegral.cycle(0))
    assert(oldIntegral(1) ==
      oldIntegral.cycle(0) + oldIntegral.cycle(1) +
        oldIntegral.initialValue)
  } else {
    assertSameBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1)
    assert(newIntegral(mergeIndex - 1) ==
      oldIntegral(mergeIndex - 1))
    assert(newIntegral(mergeIndex) ==
      newIntegral(mergeIndex - 1) +
        newIntegral.cycle(mergeIndex))
    assert(oldIntegral(mergeIndex + 1) ==
      oldIntegral(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
  }
  newIntegral(mergeIndex) == oldIntegral(mergeIndex + 1)
}.holds
```

### A.14 Removendo um Múltiplo — assertRemoveOneMultiple

Fonte: [CycleIntegralFilterProperties::assertRemoveOneMultiple](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertRemoveOneMultiple(
  oldIntegral: CycleIntegral,
  newIntegral: CycleIntegral,
  filterValue: BigInt,
  multiplePosition: BigInt
): Boolean = {
  require(filterValue > 0)
  require(multiplePosition > 0)
  require(multiplePosition + 1 < oldIntegral.period)
  require(newIntegral.period == oldIntegral.period - 1)
  require(oldIntegral.initialValue == newIntegral.initialValue)
  require(Calc.mod(oldIntegral(multiplePosition), filterValue) ==
    BigInt(0))
  require(Calc.mod(oldIntegral(0), filterValue) != BigInt(0))
  require(allGapsMatchBeforeMerge(
    oldIntegral, newIntegral, multiplePosition, multiplePosition - 1))
  require(newIntegral.cycle(multiplePosition) ==
    oldIntegral.cycle(multiplePosition) +
      oldIntegral.cycle(multiplePosition + 1))
  require(allGapsMatchAfterMerge(
    oldIntegral, newIntegral, multiplePosition, multiplePosition))
  assertShiftAtMerge(oldIntegral, newIntegral, multiplePosition)
  newIntegral(multiplePosition) ==
    oldIntegral(multiplePosition + 1)
}.holds
```

### A.15 Construção Direta a partir dos Sobreviventes — assertNewCIGeneratesFiltered

Fonte: [CycleIntegralFilterProperties::assertNewCIGeneratesFiltered](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertNewCIGeneratesFiltered(
  filteredIntegral: CycleIntegral,
  survivorList: List[BigInt],
  position: BigInt
): Boolean = {
  require(survivorList.size > position + 1)
  require(filteredIntegral.period > position)
  require(position >= 0)
  require(filteredIntegral.initialValue == survivorList.head)
  require(allGapsMatch(filteredIntegral, survivorList, position))
  decreases(position)
  if (position == 0) {
    assert(filteredIntegral(0) ==
      filteredIntegral.initialValue + filteredIntegral.cycle(0))
  } else {
    assert(allGapsMatch(filteredIntegral, survivorList, position - 1))
    assertNewCIGeneratesFiltered(
      filteredIntegral, survivorList, position - 1)
    assert(filteredIntegral(position - 1) ==
      survivorList(position))
    assert(filteredIntegral(position) ==
      filteredIntegral(position - 1) + filteredIntegral.cycle(position))
  }
  filteredIntegral(position) == survivorList(position + 1)
}.holds
```

### A.16 Resultado Filtrado Não Tem Múltiplos — assertFilterMergeComposition

Fonte: [CycleIntegralFilterProperties::assertFilterMergeComposition](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertFilterMergeComposition(
  originalCI: CycleIntegral,
  newCI: CycleIntegral,
  survivors: List[BigInt],
  filterValue: BigInt,
  maxIndex: BigInt
): Boolean = {
  require(filterValue > 0)
  require(originalCI.period > 0)
  require(Calc.mod(originalCI(0), filterValue) != BigInt(0))
  require(survivors == survivorValues(originalCI, filterValue,
    BigInt(0), originalCI.period))
  require(!survivors.isEmpty)
  require(newCI.initialValue == survivors.head)
  require(newCI.cycle.values == gapsFromValues(survivors))
  require(maxIndex >= 0)
  require(maxIndex < newCI.period)
  require(survivors.size > maxIndex + 1)
  decreases(maxIndex + 1)

  assertNewCIMatchesSurvivors(survivors, newCI, maxIndex)
  assertSurvivorAtNotMultiple(originalCI, filterValue,
    BigInt(0), originalCI.period, maxIndex + 1)

  if (maxIndex > 0) {
    assertFilterMergeComposition(originalCI, newCI,
      survivors, filterValue, maxIndex - 1)
  }
  Calc.mod(newCI(maxIndex), filterValue) != BigInt(0)
}.holds
```

### A.17 Geração pelo Ciclo Unitário — assertCycleIntegralOfOnes, assertCycleIntegralOfOnesStrictlyIncreasing

Fonte: [CycleIntegralOnesProperties](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala)

```scala
def assertCycleIntegralOfOnes(init: BigInt, pos: BigInt): Boolean = {
  require(pos >= 0)
  require(init >= 0)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  decreases(pos)
  if (pos == 0) {
    ci(0) == init + BigInt(1)
  } else {
    assert(assertCycleIntegralOfOnes(init, pos - 1))
    ci(pos) == init + pos + BigInt(1)
  }
}.holds

def assertCycleIntegralOfOnesStrictlyIncreasing(
  init: BigInt,
  a: BigInt,
  b: BigInt
): Boolean = {
  require(a >= 0)
  require(b > a)
  require(init >= 0)
  val cycle = MemCycle(stainless.collection.List(BigInt(1)))
  val ci = CycleIntegral(init, cycle)
  assert(assertCycleIntegralOfOnes(init, a))
  assert(assertCycleIntegralOfOnes(init, b))
  ci(b) > ci(a)
}.holds
```

## Apêndice B: Saída do Log de Verificação do Stainless

A execução mais recente de `just verify` verifica todas as propriedades descritas sem erros. A saída completa do log está disponível em: [logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/articles/logs/verify.log)
