# Verificação Formal de Propriedades de Integração Discreta a partir de Primeiros Princípios

**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)    
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**Licença:** [CC BY 4.0](../LICENSE)<br>
**Publicado:** [Zenodo:10.5281/zenodo.22746792](https://doi.org/10.5281/zenodo.22746792)

## Resumo

<div align="justify">
<p style="text-align: justify">

Definimos uma integral discreta recursiva sobre listas finitas de inteiros e
verificamos suas propriedades principais em Scala Stainless. Em toda posição
válida, a integral é igual ao valor inicial mais a soma prefixa correspondente;
seu valor final é igual ao valor inicial mais a soma total; e diferenças
consecutivas recuperam os valores de entrada correspondentes. Provamos a
concordância ponto a ponto, de valor final e de comprimento entre a consulta
recursiva e a representação por lista acumulada. Também verificamos que valores
de entrada positivos implicam uma integral estritamente crescente, enquanto um
gap integral consecutivo positivo implica que o valor de entrada correspondente
é positivo. Em conjunto, esses resultados caracterizam a integral discreta como
uma construção de soma cumulativa que preserva comprimento, com concordância de
representação e recuperação de valores verificadas.

</p>
</div>

## 1. Introdução

Acumulação é uma operação central em matemática e computação &mdash; de somas
prefixas em algoritmos a transformadas integrais em processamento de sinais. Em
programação funcional, a acumulação muitas vezes aparece como fold ou scan, mas
tais construções raramente são definidas a partir de primeiros princípios em um
ambiente formalmente verificado.

Neste artigo, definimos uma integral discreta recursiva sobre listas finitas de
inteiros e verificamos suas propriedades de soma cumulativa, recuperação de
diferenças, monotonicidade e concordância de representações usando Scala
Stainless. As representações por consulta recursiva e lista acumulada concordam
ponto a ponto e em comprimento, e diferenças consecutivas recuperam os valores
de entrada correspondentes.

Este artigo verifica:

- Propriedades centrais da integral: valor da cabeça, soma cumulativa, mudança incremental, soma final, crescimento estrito, positividade dos gaps — [§4.1](#41-head-value-matches-definition)–[4.6](#46-gaps-positivity)
- Consistência da implementação: concordância de elemento/acc/delta/último/tamanho entre as representações recursiva e acumulada — [§5.2](#52-element-consistency)–[5.5](#55-size-agreement)

### Trabalhos Relacionados

A construção de soma cumulativa é a instância de listas de um prefix scan ou de
uma acumulação. Em Rocq/Coq, a biblioteca padrão de listas define `fold_left` e
prova sua composição ao longo da concatenação; sua biblioteca de listas de
números naturais também define soma de listas como um fold e prova soma sobre
concatenação [[2]](#ref2). Esses resultados formalmente checados fornecem um
cenário estabelecido útil para acumulação recursiva.

O presente artigo desenvolve esse cenário para uma integral recursiva de
`BigInt` em Scala Stainless. Seu foco é a concordância de duas representações
concretas — consulta recursiva e lista acumulada — e as propriedades
correspondentes de soma cumulativa, recuperação de diferenças, comprimento e
monotonicidade. A citação situa essas provas em um tratamento formal mais amplo
de acumulação em listas; ela não substitui os resultados específicos de
concordância de representações verificados aqui.

## 2. Preliminares e Notação

Seja $L = [x_0, x_1, \dots, x_{n-1}] \in \mathbb{Z}^n$ uma lista finita e não
vazia de $n$ inteiros, em que $n = |L|$, e seja $init \in \mathbb{Z}$ um valor
inicial.

Reutilizamos várias operações básicas de listas e suas propriedades verificadas
de um artigo companheiro sobre construção recursiva de listas &mdash; [Usando Verificação Formal para Provar Propriedades de Listas Definidas Recursivamente](
https://rxiverse.org/abs/2609.0023
) [[1]](#ref1).  
Estas incluem as seguintes funções:

- $\text{sum}(L)$: computa recursivamente a soma total dos elementos de uma lista.
- $\text{head}(L)$: retorna o primeiro elemento de uma lista não vazia.
- $\text{tail}(L)$: retorna a lista sem seu primeiro elemento.
- $A \mathbin{\texttt{++}} B$: concatena duas listas $A$ e $B$.

Essas operações foram definidas e verificadas usando a mesma metodologia de
conhecimento prévio zero [[1]](#ref1), e são tratadas aqui como primitivas
fundamentais.

As provas neste artigo são escritas em Scala e verificadas usando o sistema
Stainless, com `BigInt` usado para representar inteiros ilimitados.

## 3. Definição de Integral Discreta

A integral discreta acumula valores de lista em somas parciais a partir de um
valor inicial dado. Duas representações são equivalentes.

- Matemática: $I_k = init + \sum_{i=0}^k L_i$ — a especificação
- Recursiva: $I_0 = L_0 + init$, $I_{k+1} = I_k + L_{k+1}$ — a implementação

### 3.1 Definição Matemática

Definimos a **integral discreta** $I = Integral(L, init)$ como uma lista de
somas parciais tal que:

```math
\begin{aligned}
\text{for } k \in [0, n - 1] \\
I_{k} := init + \sum_{i=0}^{k} L_i \\
\end{aligned}
```

### 3.2 Definição Recursiva

A implementação computa as mesmas somas parciais removendo uma cabeça da lista a
cada passo recursivo e carregando o valor acumulado atual.

```math
\begin{aligned}
I &:= \text{Integral}(L, init) \\
n &:= |L| \\
k &\in [0, n - 1]
\end{aligned}
```

O valor do $k\text{-ésimo}$ elemento na integral $I$ é definido recursivamente
como:

```math
I_k :=
\begin{cases}
L_0 + init & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)_{(k - 1)} & \text{if } k > 0
\end{cases}
```

Em Scala, isso é codificado em [Integral.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/Integral.scala):

```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    if (position == 0) this.head else Integral(list.tail, this.head).apply(position - 1)
  }
  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }
  // ... additional methods omitted
}
```

## 4. Propriedades Centrais da Integral

Essas identidades conectam cada valor de integral definido recursivamente à
lista finita de valores que ele acumula.

- Valor da cabeça: $I_0 = L_0 + init$ — [§4.1](#41-head-value-matches-definition)
- Soma cumulativa: $I_k = init + \sum_{i=0}^k L_i$ — [§4.2](#42-integral-equals-sum-until-position)
- Mudança incremental: $I_{p+1} - I_p = L_{p+1}$ — [§4.3](#43-incremental-change-matches-list-value)
- Soma final: $I_{n-1} = init + \text{sum}(L)$ — [§4.4](#44-final-element-equals-full-sum)

<a id="41-head-value-matches-definition"></a>

### 4.1 Valor da Cabeça Coincide com a Definição

O primeiro elemento da Integral é igual ao primeiro elemento da lista original
mais o valor inicial.

```math
I_0 = x_0 + init
```

Como:

```math
\begin{aligned}
I & \ne L_e                               & \qquad \text{[By definition: Integral is not an empty list]} \\
I_0 & = \text{head}(I)                    & \qquad \text{[List element access and indexing]} \\
\text{head}(I) & = \text{head}(L) + init  & \qquad \text{[By definition of Integral]} \\
L_0 & = \text{head}(L)                    & \qquad \text{[List element access and indexing]} \\
L_0 & = x_0                               & \qquad \text{[By definition of List]} \\
\text{head}(I) & = L_0 + init             & \qquad \text{[Substitute head}(L) \text{ by } L_0] \\
I_0 & = L_0 + init                        & \qquad \text{[Substitute head}(I) \text{ by } I_0] \\
I_0 & = x_0 + init                        & \qquad \text{[Substitute } L_0 \text{ by } x_0] \\
I_0 & = x_0 + init \quad \blacksquare     & \qquad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertHeadValueMatchDefinition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.1.

<a id="42-integral-equals-sum-until-position"></a>

### 4.2 Integral Igual à Soma até a Posição

A integral na posição $k$ é igual à soma de todos os elementos da lista até essa
posição, mais o valor inicial:

```math
\forall\ k \in [0, n-1]:\ I_k = \mathit{init} + \sum_{i=0}^{k} x_i
```

**Prova por indução em $k$**

#### Caso base: $k = 0$

```math
\begin{aligned}
\sum_{i=0}^{0} x_i &= x_0 \qquad & \text{[By definition of sum]} \\
I_0 & = \mathit{init} + x_0 \qquad & \text{[By definition of integral]} \\
    & = \mathit{init} + \sum_{i=0}^{0} x_i & \qquad \text{[Substituting } x_0] \\
\end{aligned}
```
```math
\therefore
```
```math
I_0 = \mathit{init} + \sum_{i=0}^{0} x_i \qquad \text{[Q.E.D.]}
```

#### Passo indutivo: suponha que a propriedade vale para $k-1$

```math
I_{k-1} = \mathit{init} + \sum_{i=0}^{k-1} x_i \implies I_k = \mathit{init} + \sum_{i=0}^{k} x_i
```
```math
\begin{aligned}
I_{k-1} & = \mathit{init} + \sum_{i=0}^{k-1} x_i                     \qquad & \text{[By induction]} \\ 
I_k & = I_{k-1} + L_k                                                \qquad & \text{[By definition of integral]} \\
    &= \left(\mathit{init} + \sum_{i=0}^{k-1} x_i\right) + x_k       \qquad & \text{[By induction and } L_k = x_k]  \\
    &= \mathit{init} + \left(\sum_{i=0}^{k-1} x_i + x_k\right)       \qquad & \text{[Distributivity]} \\
    &= \mathit{init} + \sum_{i=0}^{k} x_i                            \qquad & \text{[By definition of sum]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
I_k = \mathit{init} + \sum_{i=0}^{k} x_i \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertIntegralEqualsSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.2.

<a id="43-incremental-change-matches-list-value"></a>

### 4.3 Mudança Incremental Coincide com o Valor da Lista

A diferença entre dois valores consecutivos na Integral é igual ao valor
correspondente na lista original $L$.

```math
\begin{aligned}
\forall \text{ } p & \in [0,\ n-2]: \\
I_{p+1} - I_p & = L_{p+1}
\end{aligned}
```

#### Prova do Caso Base $I_1 - I_0 = x_1$

```math
\begin{aligned}
I_1    &= \text{Integral}(\text{tail}(L),\ I_0)_0           & \qquad \text{[By recursive definition for a non-first element]} \\
       &= \text{Integral}([x_1, \dots, x_n],\ I_0)_0        & \qquad \text{[By tail definition]} \\
       &= \text{head}([x_1, \dots, x_n]) + I_0              & \qquad \text{[By recursive Integral definition for the first element]} \\
       &= x_1 + I_0                                         & \qquad \text{[By head definition]} \\
I_1 - I_0 &= (x_1 + I_0) - I_0                              & \qquad \text{[Substituting for } I_1, I_0] \\
          &= x_1 + I_0 - I_0                                 & \qquad \text{[Distributivity]} \\
          &= x_1                                             & \qquad \text{[Cancellation of terms]} \\
          & \therefore \\
I_1 - I_0 &= x_1                                            & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

#### Prova do Passo Indutivo $I_{p+1} - I_p = L_{p+1}$

```math
\begin{aligned}
L &= x_0 :: \text{tail}(L)                                                                                     & \qquad \text{[List decomposition]} \\
I &= I_0 :: \text{tail}(I)                                                                                     & \qquad \text{[Integral decomposition]} \\
I_{p+1} &= I_{\text{tail},\ p}                                                             & \qquad \text{[By indexing: tail of } I \text{ at position } p] \\
I_{p+2} &= I_{\text{tail},\ p+1}                                                           & \qquad \text{[By indexing: tail of } I \text{ at position } p + 1] \\
I_{\text{tail},\ p+1} &= L_{\text{tail},\ p+1} + I_{\text{tail},\ p}                       & \qquad \text{[By recursive definition of Integral]} \\
I_{p+2} - I_{p+1} &= I_{\text{tail},\ p+1} - I_{\text{tail},\ p}                           & \qquad \text{[Substituting for } I_{p+2}, I_{p+1}] \\
                   &= (L_{\text{tail},\ p+1} + I_{\text{tail},\ p}) - I_{\text{tail},\ p}   & \qquad \text{[Substituting for } I_{\text{tail},\ p+1}] \\
                   &= L_{\text{tail},\ p+1}                                                 & \qquad \text{[Cancellation of terms]} \\
L_{p+2} &= L_{\text{tail},\ p+1}                                                           & \qquad \text{[By indexing: tail of } L \text{ at position } p + 1] \\
& \therefore \\
I_{p+2} - I_{p+1} &= L_{p+2} \quad \blacksquare                                            & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertAccDiffMatchesList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.3.

<a id="44-final-element-equals-full-sum"></a>

### 4.4 Elemento Final Igual à Soma Completa

O último elemento da Integral é igual à soma de todos os elementos da Lista mais
o valor inicial.

```math
I_{n-1} = init + \sum_{i=0}^{n-1} x_i
```

Matematicamente, este é o caso $k = n-1$ da [Seção 4.2](#42-integral-equals-sum-until-position), que prova $I_k = init + \sum_{i=0}^{k} x_i$ para todo $k$:

```math
k = n - 1 \implies I_{n-1} = init + \sum_{i=0}^{n-1} x_i \\
\therefore \\
I_{n-1} = init + \sum_{i=0}^{n-1} x_i \quad \blacksquare
```

Esta propriedade é verificada em [
  IntegralProperties::assertLastEqualsSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). A prova em Stainless é uma indução estrutural autocontida no tamanho da lista — caso base de elemento único, passo indutivo pela integral da cauda — fornecendo um argumento independente, checado por máquina, para a mesma identidade. O código Scala completo de verificação está no Apêndice A.4.

### 4.5 Integral Estritamente Crescente

Quando todo valor da lista é positivo, a integral é estritamente crescente: uma
posição posterior sempre produz um valor maior. Este é o teorema de
monotonicidade — a integral cresce a cada passo.

```math
\begin{aligned}
(\forall x \in L,\ x > 0) \;\land\; 0 \leq a < b < n \;\implies\; I_b > I_a
\end{aligned}
```

**Prova.** Faça indução em $b-a$. O caso base segue da lei de diferença
consecutiva; o passo combina a hipótese indutiva com o próximo valor positivo da
lista.

```math
\begin{aligned}
b=a+1 &\implies I_{a+1}-I_a=L_{a+1}>0 &&\text{[§4.3]} \\
       &\implies I_{a+1}>I_a, \\
I_{b-1}>I_a,\quad I_b-I_{b-1}=L_b>0
       &\implies I_b>I_{b-1}>I_a \\
\therefore\ I_b &> I_a.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

**Verificação Stainless.**

```scala
def assertIntegralStrictlyIncreasing(
  integral: Integral, a: BigInt, b: BigInt
): Boolean = {
  require(a >= 0); require(b > a); require(b < integral.list.size)
  require(ListBoundUtils.allGreaterThan(integral.list, BigInt(0)))
  integral.apply(b) > integral.apply(a)
}.holds
```

Esta propriedade é verificada em [
  IntegralProperties::assertIntegralStrictlyIncreasing
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala).

<a id="46-gaps-positivity"></a>

### 4.6 Positividade dos Gaps

Se a integral aumenta entre posições consecutivas, o elemento correspondente da
lista é positivo. O gap (diferença entre valores integrais adjacentes) tem o
mesmo sinal que o elemento subjacente da lista.

```math
\begin{aligned}
0 \leq p < n-1,\quad I_{p+1} > I_p \;\implies\; L_{p+1} > 0
\end{aligned}
```

**Prova.** A lei de diferença consecutiva identifica a diferença positiva com o
valor correspondente da lista:

```math
\begin{aligned}
I_{p+1}>I_p &\implies I_{p+1}-I_p>0 \\
I_{p+1}-I_p &= L_{p+1} &&\text{[§4.3]} \\
\therefore\ L_{p+1} &> 0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

**Verificação Stainless.**

```scala
def assertGapsPositive(integral: Integral, pos: BigInt): Boolean = {
  require(pos >= 0); require(pos + 1 < integral.list.size)
  require(integral.apply(pos + 1) > integral.apply(pos))
  integral.list(pos + 1) > BigInt(0)
}.holds
```

Esta propriedade é verificada em [
  IntegralProperties::assertGapsPositive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala).

## 5. Lemas de Consistência da Implementação

Estes lemas verificam que a implementação recursiva e sua representação
acumulada concordam internamente. Eles não introduzem novas propriedades
matemáticas, mas são essenciais para a consistência formal do software.

- Consistência de elemento: $I_k = acc_k$ — [§5.2](#52-element-consistency)
- Consistência do delta acumulado: $acc_{p+1} - acc_p = L_{p+1}$ — [§5.3](#53-accumulated-delta-consistency)
- Concordância do último elemento: $\text{last}(I) = acc_{n-1} = I_{n-1}$ — [§5.4](#54-last-element-agreement)
- Concordância de tamanho: $|acc| = |L|$ — [§5.5](#55-size-agreement)

### 5.1 Definição da Lista Acumulada

A lista acumulada representa a integral discreta como uma lista completa de
somas parciais, em vez de acesso elemento por elemento.

Seja:

```math
\begin{aligned}
& acc(L, init) \in \mathbb{Z}^{|L|} \\
& L = [x_0, x_1, \dots, x_{n-1}]
\end{aligned}
```

Então, a lista acumulada é definida recursivamente como:

```math
acc(L, init) :=
\begin{cases}
L_e & \text{if } L = L_e \\
(\text{head}(L) + init) :: acc(\text{tail}(L),\ \text{head}(L) + init) & \text{otherwise}
\end{cases}
```

A implementação completa de `Integral`, incluindo o método `acc`, está em [Integral.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/Integral.scala):

```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    if (position == 0) this.head else Integral(list.tail, this.head).apply(position - 1)
  }
  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) list else List(this.head) ++ Integral(list.tail, this.head).acc
  }
  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }
  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Integral(list.tail, this.head).acc
  }
  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }
}
```

<a id="52-element-consistency"></a>

### 5.2 Consistência de Elemento

O $k\text{-ésimo}$ elemento da Integral é igual ao $k\text{-ésimo}$ elemento da
lista acumulada.

```math
\forall \text{ } k \in [0, n-1]:\ I_k = acc_k
```

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                                           & \qquad \text{[List decomposition]} \\
&I &= (x_0 + i) :: \text{tail}(I)                                                     & \qquad \text{[Integral decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L),(x_0 + i))                & \qquad \text{[Definition of } \text{acc}] \\
&I_0 &= x_0 + i = \text{acc}_0                                                        & \qquad \text{[Base case]} \\
&I_{(p+1)} &= \text{tail}(I)_p                                                        & \qquad \text{[Tail Access Shift Left]} \\
&\text{acc}_{(p+1)} &= \text{acc}(\text{tail}(L),(x_0 + i))_p                         & \qquad \text{[Recursive accumulation]} \\
&\text{tail}(I)_p &= \text{acc}(\text{tail}(L), (x_0 + i))_p                          & \qquad \text{[Inductive hypothesis]} \\
&\implies \quad I_{p+1} &= \text{acc}_{p+1}                                           & \qquad \text{[By substitution]} \\
&& \therefore \\
&\forall p \in [0..n-1], \quad I_p &= \text{acc}_p \quad \blacksquare                 & \qquad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertAccMatchesApply
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.5.

<a id="53-accumulated-delta-consistency"></a>

### 5.3 Consistência do Delta Acumulado

A diferença entre dois valores acumulados consecutivos em `Acc` é igual ao valor
correspondente da lista original.

```math
\forall\ p \in [0, n-2]:\ \text{acc}_{p+1} - \text{acc}_p = L_{p+1}
```

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1} ]                                                           & \qquad \text{[List definition]} \\
&L &= x_0 :: \text{tail}(L)                                                                 & \qquad \text{[List decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                       & \qquad \text{[Definition of acc]} \\
&\text{acc}_0 &= x_0 + i                                                                    & \qquad \text{[Base case]} \\
&\text{acc}_1 &= x_1 + \text{acc}_0                                                         & \qquad \text{[Recursive accumulation]} \\
&\implies \quad \text{acc}_1 - \text{acc}_0 &= x_1 = L_1                                    & \qquad \text{[Cancellation]} \\
&\text{acc}_{p+1} &= x_{p+1} + \text{acc}_p                                                 & \qquad \text{[Recursive accumulation]} \\
&\implies \quad \text{acc}_{p+1} - \text{acc}_p &= x_{p+1} = L_{p+1}                        & \qquad \text{[By subtraction]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
\forall p \in [0..n-2],\quad \text{acc}_{p+1} - \text{acc}_p &= L_{p+1} \quad \blacksquare & \qquad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertAccDiffMatchesList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.6.

<a id="54-last-element-agreement"></a>

### 5.4 Concordância do Último Elemento

O último elemento da lista acumulada é igual ao último elemento da integral, que
é o elemento na posição $n-1$.

```math
\begin{aligned}
acc_{(n - 1)} & = \text{last}(I) \\
acc_{(n - 1)} & = I_{(n - 1)} \\
\end{aligned}
```

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                               & \qquad \text{[List definition]} \\
&\text{last}(L) &= \begin{cases}
&x_0 & \text{if } |L| = 1 \\
&\text{last}(\text{tail}(L)) & \text{if } |L| > 1
\end{cases}                                                                 & \qquad \text{[Definition of last]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)        & \qquad \text{[Definition of accumulation]} \\
&I &= \text{acc}(L, i)                                                       & \qquad \text{[Integral as accumulated list]} \\
\end{aligned}
```

#### Caso base: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                                   & \qquad \text{[Singleton list]} \\
&\text{acc}(L, i) &= [x_0 + i]                                                & \qquad \text{[By definition]} \\
&I &= [x_0 + i]                                                               & \qquad \text{[Integral is acc]} \\
&\text{last}(I) &= x_0 + i = acc_0 = I_0                                      & \qquad \text{[last on singleton]} \\
\end{aligned}
```

#### Passo indutivo: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                                   & \qquad \text{[List decomposition]} \\
&I &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Recursive definition]} \\
&\text{tail}(I) &= \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Tail of integral]} \\
&\text{last}(I) &= \text{last}(\text{tail}(I))                                & \qquad \text{[Recursive last]} \\
&\text{last}(\text{tail}(I)) &= \text{acc}(\text{tail}(L), x_0 + i)_{(n - 2)} & \qquad \text{[Inductive hypothesis]} \\
& &= acc_{(n - 1)}                                                            & \qquad \text{[Shifted indexing]} \\
&\implies \ \text{last}(I) &= acc_{(n - 1)} = I_{(n - 1)}                     & \qquad \text{[By substitution]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
\text{last}(I) &= acc_{(n - 1)} = I_{(n - 1)} \quad \blacksquare              & \qquad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertLast
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.7.

<a id="55-size-agreement"></a>

### 5.5 Concordância de Tamanho

O tamanho da lista acumulada é igual ao tamanho da lista original.

```math
|acc| = |L|
```

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                           & \qquad \text{[List definition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)      & \qquad \text{[Recursive accumulation]} \\
\end{aligned}
```

#### Lista Vazia: $|L| = 0$

```math
\begin{aligned}
&L &= []                                                                  & \qquad \text{[Empty list]} \\
&\text{acc}(L, i) &= []                                                   & \qquad \text{[By definition]} \\
&|\text{acc}(L, i)| &= 0 = |L|                                            & \qquad \text{[Equal size]} \\
\end{aligned}
```

#### Lista Singleton: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                               & \qquad \text{[Singleton list]} \\
&\text{acc}(L, i) &= [x_0 + i]                                            & \qquad \text{[By definition]} \\
&|\text{acc}(L, i)| &= 1 = |L|                                            & \qquad \text{[Equal size]} \\
\end{aligned}
```

#### Passo indutivo: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                               & \qquad \text{[Decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)     & \qquad \text{[Recursive call]} \\
&|\text{acc}(\text{tail}(L), x_0 + i)| &= |\text{tail}(L)|                & \qquad \text{[Inductive hypothesis]} \\
&|\text{acc}(L, i)| &= 1 + |\text{tail}(L)| = |L|                         & \qquad \text{[Cons adds 1]} \\
& & \therefore \\
&|\text{acc}(L, i)| &= |L| \quad \blacksquare                             & \qquad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  IntegralProperties::assertSizeAccEqualsSizeList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). O código Scala completo de verificação está no Apêndice A.8.

## 6. Limitações

Este artigo se apoia nas hipóteses e restrições fundamentais estabelecidas no
trabalho anterior [Usando Verificação Formal para Provar Propriedades de Listas Definidas Recursivamente](https://rxiverse.org/abs/2609.0023) [[1]](#ref1).

Especificamente:

* O foco permanece em listas de inteiros ilimitados (`BigInt`), sem suporte a tipos numéricos generalizados por abstração ou type classes.
* Funções recursivas como $sum$, $head$, $tail$ e concatenação são reutilizadas do trabalho anterior [[1]](#ref1) e não são redefinidas aqui.
* Devido à natureza recursiva dessas definições, estouros de pilha podem ocorrer com listas extensas, mas correção e verificabilidade têm prioridade sobre desempenho.

## 7. Conclusão

Este artigo estabeleceu e verificou formalmente uma caracterização por
propriedades da integral discreta recursiva sobre listas finitas de inteiros.

A partir da definição recursiva de $I = \text{Integral}(L, init)$, provamos e
verificamos:

```math
\begin{aligned}
I_0 &= x_0 + init & \text{[Head Value Matches Definition]} \\
I_k &= init + \sum_{i=0}^k x_i & \text{[Integral Equals Sum Until Position]} \\
I_{n-1} &= init + \sum_{i=0}^{n-1} x_i & \text{[Final Element Equals Full Sum]} \\
I_{p+1} - I_p &= x_{p+1} & \text{[Incremental Change Matches List]} \\
(\forall x \in L,\ x > 0) \;\land\; 0 \leq a < b < n &\implies I_b > I_a & \text{[Strictly Increasing]} \\
0 \leq p < n-1,\quad I_{p+1} > I_p &\implies L_{p+1} > 0 & \text{[Gaps Positivity]} \\
\end{aligned}
```
```math
\begin{aligned}
I_k &= acc_k & \text{[Element Consistency]} \\
\text{last}(I) &= acc_{n-1} = I_{n-1} & \text{[Last Element Agreement]} \\
acc_{p+1} - acc_p &= x_{p+1} & \text{[Accumulated Delta Consistency]} \\
|acc| &= |L| & \text{[Size Agreement]} \\
\end{aligned}
```

Esses resultados estabelecem que a integral discreta recursiva corresponde
exatamente à soma cumulativa dos elementos da lista mais o valor inicial dado. A
consulta recursiva e a representação por lista acumulada concordam em todo índice
válido, no valor final e em comprimento; suas diferenças consecutivas recuperam
as entradas correspondentes da lista original. Valores de entrada positivos
tornam a integral estritamente crescente, enquanto um gap integral consecutivo
positivo implica que o valor de entrada correspondente é positivo.

Todas as propriedades foram formalmente verificadas em Scala usando o sistema de
verificação Stainless. O código completo de verificação está no Apêndice A.

## 8. Trabalho Futuro

Estender a integral finita para sequências repetitivas de valores capturaria a
relação entre aritmética modular e decomposição gap-período — a fundação para
raciocinar sobre somas cumulativas em estruturas cíclicas.

## 9. Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>  
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*.
Disponível em: [https://rxiverse.org/abs/2609.0023](https://rxiverse.org/abs/2609.0023)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
The Rocq Development Team. *The Rocq Standard Library: Lists*.
Disponível em: [https://rocq-prover.org/doc/V8.20.0/stdlib/Coq.Lists.List.html](https://rocq-prover.org/doc/V8.20.0/stdlib/Coq.Lists.List.html)

## Apêndice A: Código de Verificação Scala

### A.1 Valor da Cabeça Coincide com a Definição — assertHeadValueMatchDefinition

Fonte: [IntegralProperties::assertHeadValueMatchDefinition](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertHeadValueMatchDefinition(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  assert(integral.head == integral.list.head + integral.init)
  assert(integral.apply(0) == integral.head)
  assert(integral.acc(0) == integral.head)
  assert(integral.acc(0) == integral.apply(0))
  integral.head == integral.list.head + integral.init
}.holds
```

### A.2 Integral Igual à Soma até a Posição — assertIntegralEqualsSum

Fonte: [IntegralProperties::assertIntegralEqualsSum](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertIntegralEqualsSum(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.nonEmpty)
  require(position >= 0 && position < integral.list.size)
  require(integral.list.size > 1)
  decreases(position)

  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))

  if (position == 0) {
    // base case
    assert(assertHeadValueMatchDefinition(integral))
    assert(ListUtils.slice(integral.list, 0, position) == List(integral.list.head))
    assert(integral.apply(0) == integral.init + ListUtils.sum(List(integral.list.head)))
    assert(integral.apply(0) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
  } else {
    // Inductive step
    assert(assertIntegralEqualsSum(integral, position - 1))
    assert(position > 0)
    assert(position < integral.list.size)
    assert(position - 1 < integral.list.size - 1)
    assert(integral.list.size == integral.acc.size)
    assert(integral.list.size > 1)
    assert(assertAccDiffMatchesList(integral, position - 1))

    val prevList = ListUtils.slice(integral.list, 0, position - 1)
    val prevSum = ListUtils.sum(prevList)
    assert(integral.apply(position - 1) == integral.init + prevSum)
    assert(integral.apply(position) == integral.apply(position - 1) + integral.list(position))
    assert(integral.apply(position) == integral.init + prevSum + integral.list(position))
    assert(ListUtils.listSumAddValue(integral.list, integral.list(position)))
    assert(ListUtilsProperties.assertAppendToSlice(integral.list, 0, position))
    assert(ListUtils.slice(integral.list, 0, position) == ListUtils.slice(integral.list, 0, position - 1) ++ List(integral.list(position)))
    assert(integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
  }
  integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position))
}.holds
```

### A.3 Mudança Incremental — assertAccDiffMatchesList

Fonte: [IntegralProperties::assertAccDiffMatchesList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertAccDiffMatchesList(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.size > 1)
  require(position >= 0 && position < integral.list.size - 1)
  decreases(position)

  if (position == 0) {
    // base case
    assert(IntegralProperties.assertAccDifferenceEqualsTailHead(integral))
    assert(integral.apply(0) == integral.acc(0))
    assert(integral.apply(1) == integral.acc(1))
    assert(
      integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
        integral.acc(position) == integral.apply(position)
    )
  } else {
    assert(position > 0)
    assert(position < integral.list.size - 1)
    assert(position - 1 < integral.list.size)

    // Inductive step
    val next = Integral(integral.list.tail, integral.head)
    assert(next.size == integral.size - 1)
    assert(integral.tail == next.acc)
    assert(assertAccDiffMatchesList(next, position - 1))

    // link this values and next values
    assert(integral.apply(position)     == next.apply(position - 1))
    assert(integral.apply(position + 1) == next.apply(position))

    assert(integral.apply(position) == integral.acc(position))
    assert(integral.apply(position + 1) == integral.acc(position + 1))
  }
  integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
    integral.acc(position + 1) == integral.apply(position + 1) &&
    integral.acc(position) == integral.apply(position)
}.holds
```

### A.4 Elemento Final Igual à Soma Completa — assertLastEqualsSum

Fonte: [IntegralProperties::assertLastEqualsSum](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertLastEqualsSum(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  decreases(integral.list.size)

  if (integral.list.size == 1) {
    // base case
    assert(integral.last == integral.list.head + integral.init)
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  } else {
    // inductive step
    val next = Integral(integral.list.tail, integral.list.head + integral.init)
    assert(assertLastEqualsSum(next))
    assert(integral.tail == next.acc)
    assert(integral.tail.last == next.acc.last)
    assert(next.last == next.acc.last)
    assert(next.last == integral.last)
    assert(next.last == next.init + ListUtils.sum(next.list))
    assert(next.last == integral.init + integral.list.head + ListUtils.sum(next.list))
    assert(integral.last == integral.init + integral.list.head + ListUtils.sum(next.list))
    assert(ListUtils.listSumAddValue(next.list, integral.list.head))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(List(integral.list.head) ++ integral.list.tail))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(integral.list))
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  }
  integral.last == integral.init + ListUtils.sum(integral.list)
}.holds
```

### A.5 Consistência de Elemento — assertAccMatchesApply

Fonte: [IntegralProperties::assertAccMatchesApply](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertAccMatchesApply(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.nonEmpty)
  require(position >= 0 && position < integral.list.size)
  decreases(position)

  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
  assert(integral.list.size == integral.acc.size)

  if (position == 0) {
    // base case
    assert(integral.apply(0) == integral.head)
    assert(integral.acc(0) == integral.head)
    integral.acc(position) == integral.apply(position)
  } else {
    // Inductive step
    assert(position > 0)
    assert(position < integral.list.size)
    assert(position - 1 < integral.list.size - 1)

    val next = Integral(integral.list.tail, integral.head)
    assert(integral.tail == next.acc)

    assert(integral.apply(position) == next.apply(position - 1))
    assert(integral.acc == List(integral.head) ++ next.acc)
    assert(integral.acc.tail == next.acc)

    assert(integral.acc.nonEmpty)
    assert(integral.list.size == integral.acc.size)
    assert(position < integral.acc.size)
    assert(ListBoundUtils.assertTailShiftLeft(integral.acc, position))
    assert(integral.acc.tail(position - 1) == integral.acc(position))
    assert(integral.acc(position) == integral.acc.tail(position - 1))
    assert(integral.acc.tail(position - 1) == next.acc(position - 1))

    assert(integral.acc(position) == next.acc(position - 1))
    assert(integral.apply(position) == next.apply(position - 1))

    assert(assertAccMatchesApply(next, position - 1))
    assert(next.acc(position - 1) == next.apply(position - 1))
    assert(integral.acc(position) == integral.apply(position))
  }
  integral.acc(position) == integral.apply(position)
}.holds
```

### A.6 Consistência do Delta Acumulado — assertAccDiffMatchesList

Fonte: [IntegralProperties::assertAccDiffMatchesList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

Esta é a mesma função do Apêndice A.3. A propriedade é usada tanto para o delta
baseado em `apply` (Seção 4.3) quanto para o delta baseado em `acc` (Seção 5.3).

### A.7 Concordância do Último Elemento — assertLast

Fonte: [IntegralProperties::assertLast](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertLast(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  assert(
    integral.last ==
      integral.acc.last
  )
  assert(ListUtilsProperties.assertLastEqualsLastPosition(integral.acc))
  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
  assert(
    integral.acc.last ==
      integral.acc(integral.acc.size - 1)
  )
  assertAccMatchesApply(integral, integral.size - 1)
  assert(
    integral.acc(integral.size - 1) ==
      integral.apply(integral.size - 1)
  )
  integral.apply(integral.size - 1) == integral.last
}.holds
```

### A.8 Concordância de Tamanho — assertSizeAccEqualsSizeList

Fonte: [IntegralProperties::assertSizeAccEqualsSizeList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertSizeAccEqualsSizeList(list: List[BigInt], init: BigInt = 0): Boolean = {
  decreases(list)

  val current = Integral(list, init)

  if (list.isEmpty) {
    // base case for empty list
    assert(current.list.size == 0)
    assert(current.acc.size == 0)
  }
  else if (list.size == 1) {
    // base case for single element list
    assert(current.list.size == 1)
    assert(current.acc.size == 1)
    assert(current.acc.size == current.list.size)
  } else {
    // inductive step for lists with more than one element
    val next = Integral(list.tail, current.head)

    assertSizeAccEqualsSizeList(next.list, next.init)
    assert(next.acc.size == next.list.size)
    assert(current.acc == List(current.head) ++ next.acc)
    assert(current.acc.size == 1 + next.acc.size)
    assert(1 + list.tail.size == list.size)
  }
  current.acc.size == current.list.size
}.holds
```

## Apêndice B: Saída do Log de Verificação Stainless

A execução mais recente de `just verify` verifica todas as propriedades
descritas sem erros. A saída completa do log está disponível em:
[logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/logs/verify.log)
