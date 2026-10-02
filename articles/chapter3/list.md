# Usando Verificação Formal para Provar Propriedades de Listas Definidas Recursivamente

**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)    
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**Licença:** [CC BY 4.0](../LICENSE)<br>
**Publicado:** [rxiVerse:2609.0023](https://rxiverse.org/abs/2609.0023)<br>
**DOI:** [10.5281/zenodo.22955771](https://doi.org/10.5281/zenodo.22955771)

## Resumo

<div align="justify">
<p style="text-align: justify">

Definimos listas finitas de inteiros recursivamente e verificamos em Scala
Stainless um cálculo de propriedades para suas operações estruturais e
aritméticas. Os resultados verificados estabelecem identidades para acesso
indexado e fatiamento, leis de soma e produto sob concatenação, divisibilidade
dos produtos de listas por seus elementos e preservação de cotas dos elementos
por append e split. Também verificamos leis de listas deslocadas que preservam o
período e relacionam valores adjacentes a gaps, junto com leis de rotação que
preservam pertinência, tamanho, soma e cotas dos elementos. Coletivamente, essas
propriedades descrevem como sequências finitas recursivas se comportam sob
decomposição, composição, agregação, cotas, deslocamentos periódicos e rotação.

</p>
</div>

## 1. Introdução

Listas são sequências finitas de valores que dão suporte a uma ampla variedade
de operações em programação funcional e declarativa. Quando combinadas com
somatório, elas formam a espinha dorsal de definições de sequências,
recorrência, acumulação e integração no domínio discreto.

Nossa abordagem espelha definições recursivas tradicionais, mas é formalmente
verificada usando [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1),
um framework de verificação para programas Scala puros que usa verificação
formal para garantir que funções definidas pelo usuário satisfaçam
pré-condições, pós-condições e invariantes dados por meio de provas
automatizadas sob todas as entradas válidas.

> Verificação formal é o ato de provar ou refutar a correção dos algoritmos
> pretendidos subjacentes a um sistema com respeito a uma certa especificação ou
> propriedade formal, usando métodos formais da matemática.
> [— Wikipédia sobre Verificação Formal](https://en.wikipedia.org/wiki/Formal_verification) [[2]](#ref2)

Este artigo verifica:

- Índice e acesso: deslocamento da cauda, último elemento — [§3](#3-index-and-access-properties)
- Fatia: recursiva, por intervalo de índices, consistência com append — [§4](#4-slice-properties)
- Soma: definição, concatenação, comutatividade, positividade — [§5](#5-sum-properties)
- Produto: definição, concatenação, comutatividade, positividade — [§6](#6-product-properties)
- Divisibilidade do produto: cabeça, todos os elementos, elemento inserido — [§7](#7-product-divisibility-properties)
- Cota e ordem: propagação de cotas inferiores e superiores por append e split — [§8](#8-bound-and-order-properties)
- Equivalência de fatias — [§9](#9-equivalence-properties)
- Lista deslocada: período, identidade de gap, translação de gap — [§10](#10-shifted-list-properties)
- Rotação: invariantes de permutação (tamanho, soma, cotas, pertinência) — [§11](#11-rotation-properties)

### Trabalhos Relacionados

Listas recursivas, acesso indexado e divisão de listas são partes há muito
estabelecidas de bibliotecas formais. A biblioteca padrão de listas de Rocq/Coq
define acesso indexado, operações de prefixo e sufixo, e prova sua lei de
reconstrução `firstn n l ++ skipn n l = l` [[3]](#ref3). A biblioteca
matemática do Lean também formaliza rotação de listas por meio de divisão e
concatenação, incluindo a redução de um índice de rotação módulo o comprimento
da lista [[4]](#ref4).

Esses desenvolvimentos prévios são pontos úteis de contato para o presente
trabalho. Eles mostram como um ambiente formal-matemático maduro trata a
estrutura familiar de listas, enquanto este artigo desenvolve e verifica o
pacote de propriedades declarado para uma implementação recursiva mínima de
`BigInt` em Scala Stainless. Em particular, o artigo traz operações estruturais
para o mesmo desenvolvimento verificado que divisibilidade de produtos, cotas
numéricas, gaps de listas deslocadas e invariantes de rotação. A comparação é
contextual, não competitiva: ela situa as provas em Stainless no corpo mais
amplo de trabalho formal e deixa claros tanto a sobreposição quanto o escopo
desta implementação.

## 2. Definições

Esta seção define o próprio modelo de lista. Uma lista é vazia ou um único valor
pareado com uma lista menor, e toda operação usada posteriormente no artigo —
tamanho, append, fatiamento, indexação, soma e produto — é definida por
recursão sobre essa mesma decomposição cabeça/cauda.

### 2.1 Construção de Listas

Seja $𝕃$ o conjunto de todas as listas sobre um conjunto $S$. Uma lista é ou a
lista vazia $L_{e}$ ou uma lista não vazia $L_{node}$, como segue:

### 2.2 Lista Vazia

Definamos uma lista vazia $L_{e}$:

```math
\begin{aligned}
L_{e} & \in 𝕃 \\
L_{e} & = [] \\
\end{aligned}
```

### 2.3 Definição Recursiva de Lista

Uma lista não vazia empacota um valor, sua **cabeça**, junto com o restante da
lista, sua **cauda**, que por sua vez é uma lista menor. Toda lista em $𝕃$ é ou
a lista vazia única ou um desses pares cabeça/cauda; portanto, a definição
abaixo constrói todo o conjunto $𝕃$ a partir do $L_e$ já definido mais esta
regra única de construção:

```math
\begin{aligned}
&\text{ head } & \in 𝕊 \\
&\text{ tail } & \in 𝕃 \\
&L_{node}(\text{head}, \text{tail}) & \in 𝕃_{node} \\
&𝕃 = \{ L_e \}  \cup \{ L_{node}(\text{head}, \text{tail}) & \mid \text{head} \in 𝕊,\ \text{tail} \in 𝕃 \} \\
\end{aligned}
```

**Terminação e referências cíclicas.** Como todas as listas neste modelo são
imutáveis, cada aplicação de $L_{\text{node}}(\text{head}, \text{tail})$
produz um valor estrutural distinto, sem possibilidade de referências cíclicas.
Funções recursivas sobre $𝕃$ terminam naturalmente, pois uma estrutura
estritamente decrescente define o tamanho.


### 2.4 Acesso a Elementos e Indexação

A decomposição cabeça/cauda dá acesso direto ao primeiro elemento de uma lista e
à sua sublista restante. A indexação estende isso um passo por vez: a posição
$0$ é a cabeça, e a posição $n > 0$ é encontrada reindexando a cauda na posição
$n - 1$; assim, alcançar o índice $n$ custa $n$ passos recursivos pela cauda. O
último elemento é o valor no último índice válido, $|L| - 1$.

```math
\begin{aligned}
\text{ if } L_{node} = [v_0, v_1, \dots, v_{n-1} ] & \implies L_{node} = (head: v_0, tail: [v_1, \dots, v_{n-1}]) \\
head(L_{node}) & = v_0 \\
tail(L_{node}) & = [v_1, \dots, v_{n-1}] \\
last(L_{node}) & = L_{node(|L| - 1)} \\
L_{node(0)} & = L_{(0)} = head(L_{node}) \\
L_{node(n)} & = L_{(n)} = tail(L_{node})({n - 1}) \text{ } \forall \text{ } n > 0 \\
\end{aligned} 
```

### 2.5 Tamanho da Lista

Com a estrutura das listas definida, agora introduzimos uma definição recursiva
para seu tamanho (ou comprimento). Definimos o tamanho de uma lista $L$, $|L|$,
como segue:

```math
|L| = \begin{cases}
0 & \text{ if } L = L_{e} \\\
1 + |tail(L)| & \text{otherwise} \\
\end{cases}
```

O tamanho de uma lista é zero para a lista vazia, ou um mais o tamanho de sua
cauda caso contrário. Provado na biblioteca nativa do Stainless em
`stainless.collection.List`.


### 2.6 Append de Listas

Sejam $A, B \in 𝕃$ sobre algum conjunto $S$. A operação de append
$A \mathbin{\texttt{++}} B$ é definida recursivamente como:

```math
\begin{aligned}
A \mathbin{\texttt{++}} B =
\begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) \mathbin{\texttt{++}} B) & \text{otherwise}
\end{cases}
\end{aligned}
```

Aplicar append de $B$ a uma lista vazia produz $B$; aplicá-lo a uma lista não
vazia mantém a cabeça de $A$ no lugar e aplica append de $B$ à cauda de $A$.
Provado na biblioteca nativa do Stainless em `stainless.collection.List`.

### 2.7 Fatia de Lista

Seja $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, com $i \leq j < n$.

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

A fatia de $i$ até $j$ mantém exatamente os elementos nas posições de $i$ até
$j$, em ordem. A implementação de `slice` está disponível em [ListUtils](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala#slice). O código Scala completo de verificação está no Apêndice A.3.

### 2.8 Soma da Lista

Seja $\text{sum} : 𝕃 \implies 𝕊$ uma função definida recursivamente:

```math
sum(L) = 
\begin{cases} 0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases}
```

A soma de uma lista vazia é zero; a soma de uma lista não vazia é sua cabeça
mais a soma de sua cauda. A implementação de `sum` está disponível em [ListUtils](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala#sum). O código Scala completo de verificação está no Apêndice A.7.

### 2.9 Produto da Lista

Seja $\text{product} : 𝕃 \implies 𝕊$ uma função definida recursivamente:

```math
product(L) = 
\begin{cases} 1 & \text{if } L = L_e \\
head(L) \cdot product(tail(L)) & \text{otherwise} \\
\end{cases}
```

O produto de uma lista vazia é um; o produto de uma lista não vazia é sua
cabeça vezes o produto de sua cauda. A implementação de `product` está
disponível em [ListProduct](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está nos Apêndices A.11 a A.15.

<a id="3-index-and-access-properties"></a>

## 3. Propriedades de Índice e Acesso

Como as posições se deslocam quando a lista é decomposta em cabeça e cauda, e
como o último elemento se relaciona com seu índice.

- [Deslocamento de acesso pela cauda](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala): $\text{tail}(L)[i] = L[i+1]$ para $i < |\text{tail}(L)|$
- [Identidade do último elemento](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala): $L[|L|-1] = \text{last}(L)$

### 3.1 Deslocamento de Acesso pela Cauda

**Lema:** Para qualquer lista $L$ com pelo menos dois elementos, acessar o
$i$-ésimo elemento de sua cauda é equivalente a acessar o $(i + 1)$-ésimo
elemento da lista.

```math
\forall \text{ } L,\ i,\quad 1 < |L|, 0 \le i < |\text{tail}(L)| \implies \text{tail}(L)_{(i)} = L_{(i + 1)}
```

Como:

$$
\begin{aligned}
L &= [x_0, x_1, x_2, \dots, x_{n - 1}]                                & \qquad \text{[List definition]} \\
L &= x_0 :: [x_1, x_2, \dots, x_{n - 1}]                                                  & \qquad \text{[Cons definition]} \\
L &= \text{head}(L) :: \text{tail}(L)                                                     & \qquad \text{[Head and Tail definition]} \\
\text{tail}(L) &= [x_1, x_2, \dots, x_{n - 1}]                        & \qquad \text{[Tail definition]} \\
\text{tail}(L)_i &= x_{i + 1} = L_{i + 1} \text{ } \forall \text{ }  0 \le i < |\text{tail}(L)|  \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

Esse deslocamento para frente é verificado em [
  ListUtilsProperties::accessTailShiftRight
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala). A forma de indexação reversa, $L_i = \text{tail}(L)_{i - 1}$ para $i > 0$, é
verificada em [
  ListBoundUtils::assertTailShiftLeft
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala). O código Scala completo de verificação está no Apêndice A.1.

### 3.2 Identidade do Último Elemento

**Lema:** O último elemento de uma lista não vazia é igual ao elemento na
posição $n - 1$, em que $n = |L|$.

```math
\forall \text{ } L,\ |L| > 0 \implies \text{last}(L) = L_{(n - 1)}
```

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                   & \qquad \text{[List definition]} \\
\end{aligned}
```

**Caso base**: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                        & \qquad \text{[Singleton list]} \\
&\text{last}(L) &= x_0 = L_0 = L_{(n - 1)}                         & \qquad \text{[Definition of last]} \\
\end{aligned}
```

**Passo indutivo**: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                        & \qquad \text{[Decomposition]} \\
&\text{last}(L) &= \text{last}(\text{tail}(L))                     & \qquad \text{[Definition of last]} \\
&\text{last}(\text{tail}(L)) &= \text{tail}(L)_{(|\text{tail}(L)| - 1)} & \qquad \text{[Inductive hypothesis]} \\
&\text{tail}(L)_{(|\text{tail}(L)| - 1)} &= L_{(|L| - 1)}          & \qquad \text{[Tail Shift Position]} \\
&\implies \ \text{last}(L) &= L_{(|L| - 1)}                      & \qquad \text{[By substitution]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
&\forall L,\ |L| > 0 \implies  \text{last}(L) &= L_{(|L| - 1)} \quad \blacksquare
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtilsProperties::assertLastEqualsLastPosition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala). O código Scala completo de verificação está no Apêndice A.2.

### 3.3 Acesso Indexado sob Concatenação

Acessar uma lista concatenada em um dado índice direciona para o lado
correspondente: um índice dentro do intervalo da lista à esquerda lê dessa lista
à esquerda no mesmo índice, e um índice igual ou posterior ao tamanho da lista à
esquerda lê da lista à direita, deslocado pelo tamanho da lista à esquerda.

```math
\begin{aligned}
0 \leq k < |A| &\implies (A \mathbin{\texttt{++}} B)_k = A_k \\
|A| \leq k < |A| + |B| &\implies (A \mathbin{\texttt{++}} B)_k = B_{(k - |A|)}
\end{aligned}
```

As duas direções são provadas por indução em $k$: o caso da esquerda remove um
elemento de cabeça por vez até que $k$ alcance $0$; o caso da direita remove
elementos de $A$ até que ela se esgote, e então indexa diretamente em $B$.

Esta propriedade é verificada em [
  ListUtilsProperties::assertAppendApplyLeft
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala) and [
  ListUtilsProperties::assertAppendApplyRight
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala).

<a id="4-slice-properties"></a>

## 4. Propriedades de Fatia

Quatro construções para extrair uma sublista por intervalo de índices — todas
equivalentes.

- [Fatia recursiva pela cauda](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala): constrói a partir do fim por prepend
- [Fatia recursiva pela cabeça](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala): constrói a partir da frente
- [Fatia por intervalo de índices](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala): acumula por posição dentro de um intervalo
- [Consistência de append da fatia](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala): adicionar um singleton preserva a estrutura da fatia

### 4.1 Fatia Recursiva pela Cauda

A fatia recursiva pela cauda constrói a sublista a partir do fim, fazendo
prepend dos elementos enquanto recorre para trás.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{slice}(L, i, j) := 
\begin{cases}
L_j :: L_e & \text{if } i = j \\
\text{slice}(L, i, j - 1) \mathbin{\texttt{++}} (L_j :: L_e) & \text{if } i < j
\end{cases}
```

**Objetivo**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{slice}(L, i, j) = L[i \dots j]
```

**Prova por indução em $j$, com $i$ fixo**

**Caso base**: $j = i$

```math
\text{slice}(L, i, i) = L_i :: L_e = L[i \dots i]
```

**Passo indutivo**: suponha

```math
\text{slice}(L, i, j - 1) = [ L_k \mid i \leq k \leq j - 1 ]
```

Mostre:

```math
\begin{aligned}
\text{slice}(L, i, j)  &= \text{slice}(L, i, j - 1) \mathbin{\texttt{++}} (L_j :: L_e) & \qquad \text{[by definition of slice]} \\
&= L[i \dots (j - 1)] \mathbin{\texttt{++}} (L_j :: L_e) & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j - 1 ] \mathbin{\texttt{++}} (L_j :: L_e) & \qquad \text{[by Specification]} \\
&= [ L_k \mid i \leq k \leq j ] & \qquad \text{[by definition of Concatenation]} \\
&= L[i \dots j] & \qquad  \text{[Q.E.D]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{slice}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

Esta propriedade é verificada em [
  ListUtils::slice
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala). A implementação e o código de verificação estão no Apêndice A.3.

### 4.2 Fatia Recursiva pela Cabeça

A fatia recursiva pela cabeça constrói a sublista a partir da frente, inserindo
elementos com cons enquanto recorre para frente.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{headRecursiveSlice}(L, i, j) :=
\begin{cases}
L_i :: L_e & \text{if } i = j \\
L_i :: \text{headRecursiveSlice}(L, i + 1, j) & \text{if } i < j
\end{cases}
```

**Objetivo**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
```

**Prova por indução em $j - i$**

**Caso base**: $i = j$

```math
\text{headRecursiveSlice}(L, i, i) = L_i :: L_e = L[i \dots i]
```

**Passo indutivo**: suponha

```math
\text{headRecursiveSlice}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
```

Mostre:

```math
\begin{aligned}
\text{headRecursiveSlice}(L, i, j) &= L_i :: \text{headRecursiveSlice}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i :: L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

Esta propriedade é verificada em [
  SliceEquivalenceLemmas::headRecursiveSlice
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala). O código Scala completo de verificação está no Apêndice A.4.

### 4.3 Fatia por Intervalo de Índices

A fatia por intervalo de índices constrói a sublista por acesso direto aos
índices, recorrendo para frente pelo intervalo de índices.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{indexRangeValues}(L, i, j) :=
\begin{cases}
L_i :: L_e & \text{if } i = j \\
L_i :: \text{indexRangeValues}(L, i + 1, j) & \text{if } i < j
\end{cases}
```

**Objetivo**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{indexRangeValues}(L, i, j) = L[i \dots j]
```

**Prova por indução em $j - i$**

**Caso base**: $i = j$

```math
\text{indexRangeValues}(L, i, i) = L_i :: L_e = L[i \dots i]
```

**Passo indutivo**: suponha

```math
\text{indexRangeValues}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
```

Mostre:

```math
\begin{aligned}
\text{indexRangeValues}(L, i, j) &= L_i :: \text{indexRangeValues}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i :: L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{indexRangeValues}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

Esta propriedade é verificada em [
  SliceEquivalenceLemmas::indexRangeValues
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala). O código Scala completo de verificação está no Apêndice A.5.

### 4.4 Consistência de Append da Fatia

**Lema:** Uma fatia de uma lista do índice $f$ até $t$ pode ser expressa como a
fatia de $f$ até $t - 1$ concatenada com o elemento no índice $t$, para
$f \le t < |L|$.

```math
\begin{aligned}
L[f \dots t] &= \text{slice}(L, f, t) \\
             &= \text{slice}(L, f, t - 1) \mathbin{\texttt{++}} (L_t :: L_e) \\
             &= L[f \dots t - 1] \mathbin{\texttt{++}} (L_t :: L_e)  \quad \blacksquare
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtilsProperties::assertAppendToSlice
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala). O código Scala completo de verificação está no Apêndice A.6.

<a id="5-sum-properties"></a>

## 5. Propriedades da Soma

A `sum` recursiva coincide com o somatório matemático, e a adição comuta sobre
a concatenação.

- [Soma coincide com somatório](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala): $\text{sum}(L) = L[0] + \cdots + L[|L|-1]$
- [Append à esquerda preserva soma](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala): $\text{sum}(x :: L) = x + \text{sum}(L)$
- [Soma sobre concatenação](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala): $\text{sum}(A \mathbin{\texttt{++}} B) = \text{sum}(A) + \text{sum}(B)$
- [Comutatividade da soma](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala): $\text{sum}(A \mathbin{\texttt{++}} B) = \text{sum}(B \mathbin{\texttt{++}} A)$

### 5.1 Soma Coincide com Somatório

Podemos provar que a função recursiva `sum` sobre uma lista $L$ coincide com a
definição matemática do somatório $\sum_{i=0}^{n-1} x_i$, em que
$L = [x_0, x_1, \dots, x_{n-1}]$ e $|L| = n$.

**Caso base**: $|L| = 0$

```math
\begin{aligned}
\text{sum}(L) &= 0 & \text{[by definition of sum]} \\
\sum L &= 0 & \text{[summation over empty list]} \\
\implies \text{sum}(L) &= \sum L \in 𝕃
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
\forall \text{ } L \in 𝕃 \\
|L| = 0 \implies \text{sum}(L) = \sum L
\end{aligned}
```

**Passo indutivo**: $|L| > 0$

Seja $P \in 𝕃$, com $P = [x_1, x_2, \dots, x_{n-1}] \in 𝕃$, e suponha:

```math
\begin{aligned}
\text{sum}(P) & = \sum_{i=1}^{n-1} x_i \in & \qquad \text{[by Inductive Hypothesis]} \\
L = x_0 :: P & = [x_0, x_1, \dots, x_{n-1}]   & \qquad \text{[by Definition of Cons]} \\
\end{aligned}
```

Podemos garantir a terminação, pois:
```math
\begin{aligned}
&|L| &= |P| + 1  & \qquad \text{[by Size Definition]} \\
&|P| &< |L|      & \qquad \text{[Size Decreases Ensures Termination]} \\
\end{aligned}
```

Vamos calcular a soma de $L$:
```math
\begin{aligned}
\text{sum}(L) &= \text{head}(L) + \text{sum}(\text{tail}(L))  & \qquad \text{[by definition of the recursive function sum]} \\
              &= x_0 + \text{sum}(P)                          & \qquad \text{[by definition of head and P]} \\
              &= x_0 + \sum_{i=1}^{n-1} x_i                   & \qquad \text{[by Inductive Hypothesis]} \\
              &= \sum_{i=0}^{n-1} x_i = \sum L                
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
\forall\text{ } L \in 𝕃 \\
|L| > 0 \implies \text{sum}(L) = \sum L
\end{aligned}
```

Logo, por indução no tamanho de $L$:

```math
\begin{aligned}
\forall \text{ } L \text{ } \in 𝕃 \\
\text{sum}(L)  = \sum L = \sum_{i=0}^{n-1} x_i  \in 𝕊  \quad \blacksquare \quad \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtils::sum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala). A implementação e o código de verificação estão no Apêndice A.7.

### 5.2 Append à Esquerda Preserva Soma

A soma de uma lista com um elemento adicionado à frente é igual ao elemento mais
a soma da lista original.

```math
\begin{aligned}
\forall \text{ } x \in 𝕊 \\
\text{sum}(x :: L) = x + \text{sum}(L) \\
\end{aligned}
```

**Prova:**

```math
\begin{aligned}
A & = x :: L  & \qquad \text{[Cons]} \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A)) & \qquad \text{[By recursive definition of sum]} \\
              & = x + \text{sum}(L) & \qquad \text{[By recursive definition of head and tail]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
\text{sum}(x :: L) & = x + \text{sum}(L)  \quad \blacksquare &  \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtils::listSumAddValue
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala). O código Scala completo de verificação está no Apêndice A.8.

### 5.3 Soma sobre Concatenação

A soma de duas listas concatenadas é igual à soma de cada lista somadas entre si.

```math
	sum(A \mathbin{\texttt{++}} B) = 	sum(A) + 	sum(B)
```

**Se a lista A está vazia**:

```math
\begin{aligned}
  A \mathbin{\texttt{++}} B & = L_e \mathbin{\texttt{++}} B & \text{[A is empty list]} \\
        & = B & \text{[By definition of concatenation]} \\
  \text{sum}(A) & = 0 & \text{[By definition of sum]} \\
  \text{sum}(A \mathbin{\texttt{++}} B) & = \text{sum}(B) & \text{[Since A} \mathbin{\texttt{++}} \text{B equals B]} \\
                    & = 0 + \text{sum}(B) \\
                    & = \text{sum}(A) + \text{sum}(B) & \text{[Since sum(A) is zero]} \\
\end{aligned}
```

**Se a lista A não está vazia**:

```math
\begin{aligned}
C & = \text{tail}(A) \mathbin{\texttt{++}} B \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A))                & \text{[By definition of sum]} \\
\text{sum}(C) & = \text{sum}(\text{tail}(A)) + \text{sum}(B)                           & \text{[Inductive Step]} \\
A \mathbin{\texttt{++}} B & = \text{head}(A) :: (\text{tail}(A) \mathbin{\texttt{++}} B)                          & \text{[By definition of head and tail]} \\
\text{sum}(A \mathbin{\texttt{++}} B) & = \text{head}(A) + \text{sum}(\text{tail}(A) \mathbin{\texttt{++}} B)      & \text{[By definition of sum]} \\
                  & = head(A) + \text{sum}(\text{tail}(A)) + \text{sum}(B) & \text{[By definition of C]} \\
                  & = \text{sum}(A) + \text{sum}(B)                        & \text{[Substituting]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
	sum(A \mathbin{\texttt{++}} B) = 	sum(A) + 	sum(B) & \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtils::listCombine
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala). O código Scala completo de verificação está no Apêndice A.9.

### 5.4 Comutatividade da Soma sobre Concatenação

A ordem da concatenação não afeta a soma total.

```math
	sum(A \mathbin{\texttt{++}} B) = sum(B \mathbin{\texttt{++}} A)
```

Como:
```math
\begin{aligned}
	sum(A \mathbin{\texttt{++}} B) & = sum(A) + sum(B)                        & \text{[Sum over Concatenation]} \\
	sum(B \mathbin{\texttt{++}} A) & = sum(B) + sum(A)                        & \text{[Sum over Concatenation]} \\
	sum(B) + sum(A) & = sum(A) + sum(B)                   & \text{[Distributive]} \\
	sum(B \mathbin{\texttt{++}} A) & = sum(A \mathbin{\texttt{++}} B)  \quad \blacksquare         & \text{[Q.E.D]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListUtils::listSwap
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala). O código Scala completo de verificação está no Apêndice A.10.

### 5.5 Positividade da Soma

Se todo elemento de uma lista não vazia é maior que zero, a soma da lista é
maior que zero.

```math
\begin{aligned}
(\forall x \in L,\, x > 0) \wedge L \neq L_e \implies \text{sum}(L) > 0
\end{aligned}
```

O caso base é a lista singleton, em que a soma é apenas o único elemento
positivo. O passo indutivo adiciona uma cabeça positiva a uma cauda cuja soma já
é conhecida como positiva pela hipótese indutiva.

Esta propriedade é verificada em [
  ListUtilsProperties::assertSumPositive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala).

<a id="6-product-properties"></a>

## 6. Propriedades do Produto

A operação de produto, da identidade singleton à distributividade sobre
concatenação e à positividade.

- [Produto singleton](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala): $\text{product}(x :: \text{empty}) = x$
- [Extração de elemento do produto](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala): $\text{product}(x :: L) = x \cdot \text{product}(L)$
- [Produto sobre concatenação](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala): $\text{product}(A \mathbin{\texttt{++}} B) = \text{product}(A) \cdot \text{product}(B)$
- [Comutatividade do produto](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala): $\text{product}(A \mathbin{\texttt{++}} B) = \text{product}(B \mathbin{\texttt{++}} A)$
- [Produto positivo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala): o produto de uma lista toda positiva é positivo

### 6.1 Produto Singleton

O produto de uma lista singleton contendo $x$ é $x$.

```math
\forall \text{ } x \in 𝕊 \\
\text{product}(x :: L_e) = x
```

**Prova:**
```math
\begin{aligned}
\text{product}(x :: L_e) &= \text{head}(x :: L_e) \cdot \text{product}(\text{tail}(x :: L_e)) & \qquad \text{[by definition of product]} \\
&= x \cdot \text{product}([]) & \qquad \text{[by definition of head and tail]} \\
&= x \cdot 1 & \qquad \text{[product of empty list is 1]} \\
&= x \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListProduct::singletonProduct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está no Apêndice A.11.

### 6.2 Extração de Elemento do Produto

Um único elemento pode ser fatorado para fora do produto de uma lista
concatenada.

```math
\forall \text{ } listA, listB \in 𝕃, \forall \text{ } e \in 𝕊 \\
\text{product}(listA \mathbin{\texttt{++}} (e :: listB)) = e \cdot \text{product}(listA \mathbin{\texttt{++}} listB)
```

**Prova por indução em $listA$**

**Caso base**: $listA = L_e$

```math
\begin{aligned}
\text{product}(L_e \mathbin{\texttt{++}} (e :: listB)) &= \text{product}(e :: listB) & \qquad \text{[by definition of append and cons]} \\
&= e \cdot \text{product}(listB) & \qquad \text{[by definition of product]} \\
&= e \cdot \text{product}(L_e \mathbin{\texttt{++}} listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

**Passo indutivo**: suponha para $listA$, prove para
$\text{head}(A) :: listA$.

Esta propriedade é verificada em [
  ListProduct::productPullOutElement
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está no Apêndice A.12.

### 6.3 Produto sobre Concatenação

O produto distribui sobre a concatenação de listas.

```math
\forall \text{ } listA, listB \in 𝕃 \\
\text{product}(listA \mathbin{\texttt{++}} listB) = \text{product}(listA) \cdot \text{product}(listB)
```

**Prova por indução em $listA$**

**Caso base**: $listA = L_e$

```math
\begin{aligned}
\text{product}(L_e \mathbin{\texttt{++}} listB) &= \text{product}(listB) & \qquad \text{[by definition of append]} \\
&= 1 \cdot \text{product}(listB) & \qquad \text{[1 is multiplicative identity]} \\
&= \text{product}(L_e) \cdot \text{product}(listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

**Passo indutivo**: Para $\text{head}(A) :: listA$, a definição recursiva do
produto e a hipótese indutiva dão o resultado.

Esta propriedade é verificada em [
  ListProduct::productConcatLemma
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está no Apêndice A.13.

### 6.4 Comutatividade do Produto

O produto é invariante sob a troca de blocos concatenados.

```math
\forall \text{ } listA, listB \in 𝕃 \\
\text{product}(listA \mathbin{\texttt{++}} listB) = \text{product}(listB \mathbin{\texttt{++}} listA)
```

**Prova:**
```math
\begin{aligned}
\text{product}(listA \mathbin{\texttt{++}} listB) &= \text{product}(listA) \cdot \text{product}(listB) & \qquad \text{[Product over Concatenation]} \\
\text{product}(listB \mathbin{\texttt{++}} listA) &= \text{product}(listB) \cdot \text{product}(listA) & \qquad \text{[Product over Concatenation]} \\
&= \text{product}(listA) \cdot \text{product}(listB) & \qquad \text{[Commutativity of multiplication]} \\
&= \text{product}(listA \mathbin{\texttt{++}} listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListProduct::productConcatCommutative
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está no Apêndice A.14.

### 6.5 Produto Positivo

Se todo elemento de uma lista é estritamente positivo, então o produto é
estritamente positivo.

```math
\forall \text{ } elements \in 𝕃 \\
(\forall \text{ } x \in elements,\ x > 0) \implies \text{product}(elements) > 0
```

**Prova por indução em $elements$**

**Caso base**: $elements = L_e$

```math
\begin{aligned}
\text{product}(L_e) &= 1 > 0 \quad \blacksquare
\end{aligned}
```

**Passo indutivo**: Para $\text{head}(e) :: tail$, temos $e > 0$ e
$\text{product}(tail) > 0$ pela hipótese indutiva. O produto de dois números
positivos é positivo.

Esta propriedade é verificada em [
  ListProduct::positiveProduct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala). O código Scala completo de verificação está no Apêndice A.15.

<a id="7-product-divisibility-properties"></a>

## 7. Propriedades de Divisibilidade do Produto

Todo elemento de uma lista divide seu produto total. As provas abaixo aplicam a
lei de invariância do quociente sob deslocamento
$\text{mod}(a + m \cdot b, b) = \text{mod}(a, b)$ em $a = 0$ para derivar
$(a \cdot b) \bmod a = 0$; essa lei é verificada no artigo companheiro
[Divisão e Módulo por Normalização Recursiva](http://ai.viXra.org/abs/2609.0009) [[5]](#ref5)
e reutilizada aqui como primitiva fundamental.

- [Cabeça divide o produto](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala): $\text{product}(L) \bmod \text{head}(L) = 0$
- [Todos os elementos dividem o produto](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala): todo elemento divide $\text{product}(L)$
- [Elemento inserido divide o produto](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala): $x$ divide $\text{product}(x :: L)$

### 7.1 A Cabeça Divide o Produto

A cabeça de uma lista positiva divide o produto da lista inteira.

```math
\forall \text{ } elements \in 𝕃,\ elements \neq L_e \\
(\forall \text{ } x \in elements,\ x > 0) \implies \text{product}(elements) \bmod \text{head}(elements) = 0
```

**Prova:**
```math
\begin{aligned}
\text{product}(elements) &= \text{head}(elements) \cdot \text{product}(\text{tail}(elements)) & \qquad \text{[by definition of product]} \\
\text{product}(elements) \bmod \text{head}(elements) &= (\text{head}(elements) \cdot \text{product}(\text{tail}(elements))) \bmod \text{head}(elements) \\
&= 0 \quad \blacksquare & \qquad \text{[by modulo identity]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListProductDiv::ListProductDiv
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala). O código Scala completo de verificação está no Apêndice A.16.

### 7.2 Todos os Elementos Dividem o Produto

Todo elemento de uma lista positiva divide o produto da lista.

```math
\forall \text{ } elements \in 𝕃 \\
(\forall \text{ } x \in elements,\ x > 0) \implies (\forall \text{ } x \in elements,\ \text{product}(elements) \bmod x = 0)
```

**Prova por indução em $elements$**

**Caso base**: $elements = L_e$ — verdadeiro vacuamente.

**Passo indutivo**: Para $\text{head}(p) :: tail$, temos
$\text{product}(elements) = p \cdot \text{product}(tail)$. Pela identidade de
módulo, $p$ divide o produto. Pela hipótese indutiva, todo elemento de $tail$
aparece como cabeça de alguma sublista recursiva e divide o produto dessa
sublista. Multiplicar esse produto de sublista pelos fatores positivos
precedentes preserva a divisibilidade, portanto todo elemento da cauda também
divide $p \cdot \text{product}(tail) = \text{product}(elements)$.

Esta propriedade é verificada em [
  ListProductDiv::allElementsDivideProduct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala). O código Scala completo de verificação está no Apêndice A.17.

### 7.3 Elemento Inserido Divide o Produto

Inserir um elemento em uma lista garante que o produto resultante é divisível
por esse elemento.

```math
\forall \text{ } prefix, suffix \in 𝕃,\ \forall \text{ } e \in 𝕊,\ e > 0 \\
(\forall \text{ } x \in prefix,\ x > 0),\ (\forall \text{ } x \in suffix,\ x > 0) \\
\implies \text{product}(prefix \mathbin{\texttt{++}} (e :: suffix)) \bmod e = 0
```

**Prova:**
```math
\begin{aligned}
\text{product}(prefix \mathbin{\texttt{++}} (e :: suffix)) &= e \cdot \text{product}(prefix \mathbin{\texttt{++}} suffix) & \qquad \text{[Product Pull-Out Element]} \\
&= e \cdot k & \qquad \text{[where k = product(prefix} \mathbin{\texttt{++}} \text{suffix)]} \\
\text{product}(prefix \mathbin{\texttt{++}} (e :: suffix)) \bmod e &= (e \cdot k) \bmod e = 0 \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

Esta propriedade é verificada em [
  ListProductDiv::insertedElementDividesProduct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala). O código Scala completo de verificação está no Apêndice A.18.

<a id="8-bound-and-order-properties"></a>

## 8. Propriedades de Cota e Ordem

Como a propriedade $\forall x \in L,\, x > v$ se propaga de uma lista inteira
para seus elementos e através da concatenação.

- [Todos maiores que no índice](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala): $(\forall x \in L,\, x > v) \implies L(pos) > v$
- [Append preserva todos maiores que](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala): $(\forall x \in A,\, x > v) \wedge (\forall x \in B,\, x > v) \implies \forall x \in (A \mathbin{\texttt{++}} B),\, x > v$
- [Todos maiores que na cabeça e na cauda](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala): a decomposição cabeça/cauda propaga a cota
- [Lemas de checagem por índice](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala): verificação eficiente de cotas

### 8.1 Todos Maiores que no Índice

Para toda lista em que todos os elementos são maiores que um valor, qualquer
elemento em uma posição válida também é maior que esse valor.

```math
\forall \text{ } list \in 𝕃,\ \forall \text{ } value \in 𝕊,\ \forall \text{ } pos \in ℕ,\ pos < |list| \\
(\forall x \in list,\, x > value) \implies list(pos) > value
```

Esta propriedade é verificada em [
  ListBoundUtils::assertGreaterThanAtIndex
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala). O código Scala completo de verificação está no Apêndice A.19.

### 8.2 Append Preserva Todos Maiores que

Se ambas as listas têm todos os elementos maiores que um valor, então sua
concatenação também tem todos os elementos maiores que esse valor.

```math
\forall \text{ } listA, listB \in 𝕃,\ \forall \text{ } value \in 𝕊 \\
(\forall x \in listA,\, x > value) \wedge (\forall x \in listB,\, x > value) \\
\implies \forall x \in (listA \mathbin{\texttt{++}} listB),\, x > value
```

Esta propriedade é verificada em [
  ListBoundUtils::assertAppendGreaterThan
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala). O código Scala completo de verificação está no Apêndice A.20.

### 8.3 Todos Maiores que na Cabeça e na Cauda

Para uma lista não vazia em que todos os elementos são maiores que um valor, a
cabeça é maior que esse valor e a cauda também satisfaz a propriedade.

```math
\forall \text{ } list \in 𝕃,\ list \neq L_e,\ \forall \text{ } value \in 𝕊 \\
(\forall x \in list,\, x > value) \implies list.head > value \wedge (\forall x \in list.tail,\, x > value)
```

Esta propriedade é verificada em [
  ListBoundUtils::assertGreaterThanHeadTail
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala). O código Scala completo de verificação está no Apêndice A.21.

### 8.4 Checar Todos Maiores no Índice

Para toda lista em que todos os elementos são maiores que um valor, qualquer
elemento em uma posição válida também é maior.

```math
\forall \text{ } list \in 𝕃,\ \forall \text{ } value \in 𝕊,\ \forall \text{ } pos \in ℕ,\ pos < |list| \\
\text{checkAllBiggerThanValue}(list, value) \implies list(pos) > value
```

Esta propriedade é verificada em [
  ListUtilsProperties::checkAllBiggerThanValueAtIndex
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala). O código Scala completo de verificação está no Apêndice A.22.

### 8.5 Checar Todos Maiores na Cabeça e na Cauda

Para uma lista não vazia em que todos os elementos são maiores que um valor, a
cabeça é maior e a cauda também satisfaz a propriedade.

```math
\forall \text{ } list \in 𝕃,\ list \neq L_e,\ \forall \text{ } value \in 𝕊 \\
\text{checkAllBiggerThanValue}(list, value) \implies list.head > value \wedge \text{checkAllBiggerThanValue}(list.tail, value)
```

Esta propriedade é verificada em [
  ListUtilsProperties::checkAllBiggerThanValueHeadTail
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala). O código Scala completo de verificação está no Apêndice A.23.

### 8.6 Split Preserva Todos Maiores que

Dividir uma lista limitada inferiormente em qualquer índice válido preserva a
cota nas duas metades.

```math
\forall \text{ } list \in 𝕃,\ \forall \text{ } value \in 𝕊,\ 0 \leq index \leq |list| \\
(\forall x \in list,\, x > value) \implies (\forall x \in front,\, x > value) \wedge (\forall x \in back,\, x > value) \\
\text{where } (front, back) = \text{splitAt}(list, index)
```

Esta propriedade é verificada em [
  ListBoundUtils::assertSplitAtPreservesAllGreaterThan
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala).

### 8.7 A Família Todos Menores que

O espelho por cota superior da propriedade acima, $\forall x \in L,\, x < b$,
satisfaz o mesmo formato de propriedades: preservação por append, preservação
por split e transitividade para uma cota mais frouxa.

```math
(\forall x \in listA,\, x < bound) \wedge (\forall x \in listB,\, x < bound) \implies \forall x \in (listA \mathbin{\texttt{++}} listB),\, x < bound \quad \text{[Append]}
```

```math
\forall \text{ } index \in ℕ,\ index \leq |list|
```

```math
(\forall x \in list,\, x < bound) \implies (\forall x \in front,\, x < bound) \wedge (\forall x \in back,\, x < bound) \quad \text{[Split]}
```

```math
(\forall x \in list,\, x < bound) \wedge bound \leq bound_2 \implies \forall x \in list,\, x < bound_2 \quad \text{[Transitivity]}
```

```math
\forall \text{ } pos \in ℕ,\ pos < |list|
```

```math
(\forall x \in list,\, x < bound) \implies list(pos) < bound \quad \text{[At Index]}
```

Essas propriedades são verificadas em [
  ListBoundUtils::assertAppendLessThan
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala), [
  ListBoundUtils::assertSplitAtPreservesAllLessThan
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala), [
  ListBoundUtils::assertTransitiveLessThan
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala), e [
  ListBoundUtils::assertLessThanAtIndex
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala).

<a id="9-equivalence-properties"></a>

## 9. Propriedades de Equivalência

Todas as três construções de fatia produzem resultados idênticos para toda
entrada válida.

- [Equivalência de fatias](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala): as fatias recursiva pela cauda, recursiva pela cabeça e por intervalo de índices são idênticas para todas as entradas válidas

### 9.1 Lema de Equivalência de Fatias

Todas as três implementações de fatia — recursiva pela cauda, recursiva pela
cabeça e por intervalo de índices — produzem o mesmo resultado para qualquer
entrada válida.

```math
\forall \text{ } L \in 𝕃,\ \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \\
\text{slice}(L, i, j) = \text{headRecursiveSlice}(L, i, j) = \text{indexRangeValues}(L, i, j)
```

**Prova por indução em $j - i$**

**Caso base**: $i = j$ — todas as três produzem $L_i :: L_e$.

**Passo indutivo**: Para $i < j$, cada função se decompõe em um elemento de
cabeça mais uma chamada recursiva em $(i+1, j)$ ou $(i, j-1)$. Pela hipótese
indutiva, as chamadas recursivas produzem sublistas iguais, e o elemento de
cabeça é o mesmo; portanto, os resultados são iguais.

Esta propriedade é verificada em [
  SliceEquivalenceLemmas::tailHeadAndIndexRangeSlicesAreEqual
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala). O código Scala completo de verificação está no Apêndice A.24.

<a id="10-shifted-list-properties"></a>

## 10. Propriedades de Lista Deslocada

Uma lista deslocada avança a cabeça por um gap e reindexa as posições. Três
lemas caracterizam essa operação.

- [Mesmo período](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala): deslocar não altera o período (comprimento da lista de gaps)
- [Diferença adjacente igual ao gap](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala): valores consecutivos da lista deslocada diferem pelo gap correspondente
- [Translação de gap](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala): deslocar translada a sequência de gaps por um índice

Uma lista deslocada é uma sequência de valores vista uma posição adiante, com a
cabeça avançada pelo primeiro gap. Diferentemente da rotação (que reindexa sem
alterar valores), um deslocamento muda a cabeça e reindexa posições.

Deslocar é a operação no nível de lista que avança uma posição em uma sequência
cumulativa de valores. Quando uma sequência de diferenças adjacentes é conhecida
(a lista de gaps), avançar a cabeça pelo primeiro gap e rotacionar a lista de
gaps produz a vista a partir da próxima posição — sem recomputar as somas
cumulativas.

```math
\begin{aligned}
\text{ShiftedList}(h,\; [g_0,\dots,g_{n-1}]) &: \text{head} = h,\; \text{gaps} = [g_0,\dots,g_{n-1}] \\
\text{value}_{h,G}(0) &= h \\
\text{value}_{h,G}(i + 1) &= \text{value}_{h,G}(i) + G_i \\
\text{shift}(h,\; [g_0,\dots,g_{n-1}]) &= \text{ShiftedList}(h + g_0,\; [g_1,\dots,g_{n-1}, g_0])
\end{aligned}
```

### 10.1 Mesmo Período

Deslocar não altera o período: a lista de gaps permanece com o mesmo
comprimento. A propriedade estrutural $\text{size} = |\text{gaps}|$ é um
invariante da case class.

```math
\begin{aligned}
\text{period}(\text{shifted}) = \text{period}(\text{original}) \quad &\text{[Q.E.D.]}
\end{aligned}
```

Fonte: [ShiftedList::assertSamePeriod](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala)

```scala
def assertSamePeriod(otherSize: BigInt): Boolean = {
  require(otherSize == gaps.size)
  size == otherSize
}.holds
```

### 10.2 Diferença Adjacente Igual ao Gap

Para qualquer posição válida, a diferença entre valores consecutivos da lista
deslocada é igual ao gap nessa posição. Isso é consequência direta da definição
cumulativa de valor acima.

```math
\begin{aligned}
\text{value}_{h,G}(i + 1) - \text{value}_{h,G}(i) = G_i
\quad \text{for } 0 \leq i < \text{size} - 1 \quad &\text{[Q.E.D.]}
\end{aligned}
```

Fonte: [ShiftedList::assertAdjacentDifferenceEqualsGap](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala)

```scala
def assertAdjacentDifferenceEqualsGap(position: BigInt): Boolean = {
  require(position >= 0)
  require(position + 1 < size)
  apply(position + 1) - apply(position) == gaps(position)
}.holds
```

### 10.3 Translação de Gap

Deslocar a cabeça e rotacionar os gaps por um translada a sequência de gaps
adjacentes por um índice: o gap da sequência deslocada em $i$ é igual ao gap da
sequência original em $i + 1$. Ambos os lados reduzem a $G_{i+1}$ porque a lista
de gaps é rotacionada por uma posição.

```math
\begin{aligned}
\text{value}_{\text{shift}(h,G)}(i + 1) - \text{value}_{\text{shift}(h,G)}(i)
  &= \text{value}_{h,G}(i + 2) - \text{value}_{h,G}(i + 1)
  && \text{[Gap translation]} \\
  &= \text{gaps}(i + 1)
  && \text{[By adjacent-difference identity for both views]}
\end{aligned}
```

Fonte: [ShiftedList::assertGapTranslation](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala)

```scala
def assertGapTranslation(
  origHead: BigInt, gaps: List[BigInt], i: BigInt
): Boolean = {
  require(gaps.nonEmpty)
  require(i >= 0)
  require(i + 2 < gaps.size)
  val shifted = shift(origHead, gaps)
  val orig = ShiftedList(origHead, gaps)
  shifted.apply(i + 1) - shifted.apply(i) ==
    orig.apply(i + 2) - orig.apply(i + 1)
}.holds
```

Essas propriedades são verificadas em [
  ShiftedList::assertSamePeriod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala), [
  ShiftedList::assertAdjacentDifferenceEqualsGap
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala), e [
  ShiftedList::assertGapTranslation
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ShiftedList.scala).

<a id="11-rotation-properties"></a>

## 11. Propriedades de Rotação

A permutação cíclica preserva todo invariante estrutural: os mesmos elementos,
o mesmo tamanho, a mesma soma e as mesmas cotas.

- [Mesmos elementos](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala): $\text{rotateAt}(L, k).\text{contains}(x) \iff L.\text{contains}(x)$
- [Mesmo tamanho e soma](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala): $|\text{rotateAt}(L, k)| = |L|$, $\sum \text{rotateAt}(L, k) = \sum L$
- [Preservação de cotas](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala): $(\forall x \in L,\, x > v) \implies \forall x \in \text{rotateAt}(L, k),\, x > v$, e de modo análogo para a cota superior $\forall x \in L,\, x < b$
- [Deslocamento de índice por um](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala): $\text{rotateAt}(L, 1)(i) = L(i + 1)$

Rotacionar uma lista no índice `k` troca a frente (os primeiros `k` elementos)
com o fundo (os elementos restantes) — uma permutação cíclica. A rotação
preserva todo invariante estrutural: tamanho, soma, pertinência de elementos e
propriedades de cota permanecem inalterados, porque o multiconjunto de elementos
é o mesmo sob qualquer reordenação cíclica.

Permutações cíclicas surgem sempre que um conjunto fixo de valores é visto a
partir de uma posição inicial diferente — por exemplo, ao deslocar um buffer
circular ou alinhar uma sequência periódica. A invariância por rotação significa
que nenhuma propriedade estrutural é perdida quando a janela de observação se
move.

```math
\begin{aligned}
\text{rotateAt}(L,\; k) &= \text{back} \mathbin{\texttt{++}} \text{front}
  \quad\text{where } (\text{front},\; \text{back}) = \text{splitAt}(L, k) \\
  &= [L_k, L_{k+1}, \ldots, L_{n-1}, L_0, L_1, \ldots, L_{k-1}]
\end{aligned}
```

### 11.1 Invariantes de Permutação

A rotação é uma permutação do multiconjunto subjacente: os mesmos elementos
aparecem, e toda quantidade estrutural derivada da lista é preservada.

**Pertinência.** Um elemento pertence à lista original se e somente se pertence
à lista rotacionada. Como a ordem de `append` não afeta a pertinência, trocar
`front` e `back` preserva o conjunto de elementos.

```math
\begin{aligned}
\text{rotateAt}(L, k).\text{contains}(x) &\iff L.\text{contains}(x)
  &&\text{[Q.E.D.]}
\end{aligned}
```

**Tamanho e soma.** A lista rotacionada tem o mesmo comprimento e a mesma soma
total. A soma sobre `append` é aditiva e comutativa.

```math
\begin{aligned}
|\text{rotateAt}(L, k)| &= |L| &&\text{[Same size]} \\
\sum \text{rotateAt}(L, k) &= \sum L &&\text{[Same sum]}
\end{aligned}
```

**Preservação de cotas.** Se todo elemento de `L` é estritamente maior que `v`
(ou estritamente menor que `b`), o mesmo vale após a rotação.

```math
\begin{aligned}
(\forall x \in L,\, x > v) &\implies \forall x \in \text{rotateAt}(L, k),\, x > v \\
(\forall x \in L,\, x < b) &\implies \forall x \in \text{rotateAt}(L, k),\, x < b
\end{aligned}
```

### 11.2 Deslocamento de Índice sob Rotação por Um

Rotacionar por uma posição e consultar o índice $k$ dá o elemento da lista
original no índice $k + 1$. Este é o lema subjacente à translação de gaps em
`ShiftedList`.

```math
\begin{aligned}
\text{rotateAt}(L, 1)(k) = L(k + 1) \quad \text{for } k + 1 < |L| \quad &
\text{[Q.E.D.]}
\end{aligned}
```

Fonte: [RotationProperties](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala)

```scala
def assertRotateContainsForward(
  list: List[BigInt], index: BigInt, x: BigInt
): Boolean = {
  require(index >= 0); require(list.contains(x))
  ListUtils.rotateAt(list, index).contains(x)
}.holds

def assertRotateSameSize(list: List[BigInt], index: BigInt): Boolean = {
  require(index >= 0)
  ListUtils.rotateAt(list, index).size == list.size
}.holds

def assertRotateSameSum(list: List[BigInt], index: BigInt): Boolean = {
  require(index >= 0)
  ListUtils.sum(ListUtils.rotateAt(list, index)) == ListUtils.sum(list)
}.holds

def assertRotateSameLowerBound(
  list: List[BigInt], index: BigInt, value: BigInt
): Boolean = {
  require(index >= 0); require(ListBoundUtils.allGreaterThan(list, value))
  ListBoundUtils.allGreaterThan(ListUtils.rotateAt(list, index), value)
}.holds

def assertRotatedAtIndexPlusOne(list: List[BigInt], k: BigInt): Boolean = {
  require(k + 1 < list.size)
  ListUtils.rotateAt(list, BigInt(1)).apply(k) == list.apply(k + 1)
}.holds
```

Essas propriedades são verificadas no módulo [
  RotationProperties
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala) (11 lemas no total). O par de pertinência direta/inversa e o par
de cotas superior/inferior cobrem todos os invariantes de permutação; os lemas
restantes (`assertAppendContainsLeft/Right/Decompose/Swap`) são auxiliares
estruturais consumidos pelas provas principais de rotação.

## 12. Conclusão

Este artigo estabeleceu um cálculo de propriedades formalmente verificado para
listas finitas de inteiros representadas por decomposição recursiva
cabeça-cauda.

As propriedades centrais provadas podem ser resumidas como segue, para listas
$L,A,B,P,S \in 𝕃$, valores $x,e,v \in 𝕊$ e índices naturais válidos.

```math
\begin{aligned}
|L| > 0
&\implies L_{|L|-1} = \text{last}(L)
&&\text{[Last Element Identity]} \\
0 < i < |L|
&\implies L_i = \text{tail}(L)_{i-1}
&&\text{[Tail Access Shift]} \\
0 \leq f < t < |L|
&\implies L[f \dots t]
 = L[f \dots (t - 1)] \mathbin{\texttt{++}} (L_t :: L_e)
&&\text{[Slice Append Consistency]}
\end{aligned}
```

```math
\begin{aligned}
\text{sum}(L)
&= \sum_{i=0}^{|L|-1} L_i
&&\text{[Sum Matches Summation]} \\
\text{sum}(x :: L)
&= x + \text{sum}(L)
&&\text{[Left Append Preserves Sum]} \\
\text{sum}(A \mathbin{\texttt{++}} B)
&= \text{sum}(A) + \text{sum}(B)
&&\text{[Sum over Concatenation]} \\
\text{sum}(A \mathbin{\texttt{++}} B)
&= \text{sum}(B \mathbin{\texttt{++}} A)
&&\text{[Commutativity of Sum]} \\
(\forall x \in L,\ x > 0) \land L \neq L_e
&\implies \text{sum}(L) > 0
&&\text{[Sum Positivity]}
\end{aligned}
```

```math
\begin{aligned}
\text{product}(x :: L_e)
&= x
&&\text{[Singleton Product]} \\
\text{product}(A \mathbin{\texttt{++}} (e :: B))
&= e \cdot \text{product}(A \mathbin{\texttt{++}} B)
&&\text{[Product Pull-Out Element]} \\
\text{product}(A \mathbin{\texttt{++}} B)
&= \text{product}(A) \cdot \text{product}(B)
&&\text{[Product over Concatenation]} \\
\text{product}(A \mathbin{\texttt{++}} B)
&= \text{product}(B \mathbin{\texttt{++}} A)
&&\text{[Commutativity of Product]} \\
(\forall x \in L,\ x > 0)
&\implies \text{product}(L) > 0
&&\text{[Positive Product]}
\end{aligned}
```

```math
\begin{aligned}
L \neq L_e \land (\forall x \in L,\ x > 0)
&\implies \text{product}(L) \bmod \text{head}(L) = 0
&&\text{[Head Divides Product]} \\
(\forall x \in L,\ x > 0)
&\implies \forall x \in L,\ \text{product}(L) \bmod x = 0
&&\text{[All Elements Divide Product]} \\
e > 0 \land (\forall x \in P,\ x > 0) \land (\forall x \in S,\ x > 0)
&\implies \text{product}(P \mathbin{\texttt{++}} (e :: S)) \bmod e = 0
&&\text{[Inserted Element Divides Product]}
\end{aligned}
```

```math
\begin{aligned}
(\forall x \in L,\ x > v) \land 0 \leq i < |L|
&\implies L_i > v
&&\text{[Bound at Index]} \\
(\forall x \in A,\ x > v) \land (\forall x \in B,\ x > v)
&\implies \forall x \in A \mathbin{\texttt{++}} B,\ x > v
&&\text{[Bound over Concatenation]} \\
(\forall x \in L,\ x > v) \land 0 \leq k \leq |L|
&\implies (\forall x \in \text{front},\ x > v) \land (\forall x \in \text{back},\ x > v)
&&\text{[Split Preserves Lower Bound]} \\
(\forall x \in A,\ x < b) \land (\forall x \in B,\ x < b)
&\implies \forall x \in A \mathbin{\texttt{++}} B,\ x < b
&&\text{[Bound over Concatenation, Upper]} \\
(\forall x \in L,\ x < b) \land 0 \leq k \leq |L|
&\implies (\forall x \in \text{front},\ x < b) \land (\forall x \in \text{back},\ x < b)
&&\text{[Split Preserves Upper Bound]} \\
\text{slice}(L,f,t)
&= \text{headRecursiveSlice}(L,f,t)
 = \text{indexRangeValues}(L,f,t)
&&\text{[Slice Equivalence]}
\end{aligned}
```

```math
\begin{aligned}
\text{value}_{h,G}(i + 1) - \text{value}_{h,G}(i)
&= G_i
&&\text{[Adjacent Difference]} \\
\text{value}_{\text{shift}(h,G)}(i + 1)
 - \text{value}_{\text{shift}(h,G)}(i)
&= \text{value}_{h,G}(i + 2) - \text{value}_{h,G}(i + 1)
&&\text{[Gap Translation]} \\
\text{rotateAt}(L,k).\text{contains}(x)
&\iff L.\text{contains}(x)
&&\text{[Rotation Same Elements]} \\
|\text{rotateAt}(L,k)|
&= |L|
&&\text{[Rotation Same Size]} \\
\text{sum}(\text{rotateAt}(L,k))
&= \text{sum}(L)
&&\text{[Rotation Same Sum]}
\end{aligned}
```

Todas essas propriedades são verificadas nas referências de código-fonte citadas
ao longo do artigo. O Apêndice A reúne os trechos Scala que são úteis manter
próximos ao texto; cada trecho aponta de volta para seu arquivo-fonte mantido.

Coletivamente, esses resultados fornecem um cálculo verificado para decompor e
compor listas finitas, agregar e limitar seus valores, relacionar seus elementos
a produtos de listas, preservar período enquanto se rastreiam valores adjacentes
e gaps sob transformações de listas deslocadas, e preservar pertinência,
tamanho, soma e cotas de elementos sob rotação.

## 13. Trabalho Futuro

Estender listas por integração (somas cumulativas) e derivação (extração de
gaps) formalizaria duas operações duais que mapeiam entre uma lista e sua forma
acumulada ou decomposta. Essas operações conectam a álgebra de listas finitas
apresentada aqui à teoria de sequências e diferenças discretas.

Duas disciplinas relacionadas de listas têm provas verificadas no código-fonte,
mas não são desenvolvidas aqui como propriedades principais: manter ordem
ascendente sob inserção e filtragem (`SortedList`), e preservar uma cota
numérica inferior ou superior apenas sob filtragem, em vez das operações de
append/split cobertas em [§8](#8-bound-and-order-properties) (`MinBoundList`,
`MaxBoundList`). Um tratamento dedicado de variantes de listas ordenadas e de
filtro limitado fica como trabalho futuro.

## 14. Limitações

Este artigo restringe a implementação e a verificação a listas finitas e
imutáveis de inteiros representadas usando o tipo de dados
`stainless.collection.List`. O foco está na **correção**, não em desempenho ou
escalabilidade. Nossos modelos de somatório e acumulação seguem uma
**definição recursiva**, alinhada ao formalismo matemático. Contudo, essa
abordagem pode introduzir limitações de desempenho em aplicações práticas que
envolvem listas grandes.

### 14.1 Overflow e Limites de Memória Estão Fora do Escopo

Ao usar `BigInt` e listas imutáveis, o modelo assume aritmética inteira
ilimitada e capacidade infinita de listas. Essa escolha evita erros de overflow
e falta de memória, mas não reflete as restrições de tipos inteiros de tamanho
fixo ou de memória de sistema limitada em ambientes reais.

### 14.2 Efeitos Colaterais São Excluídos

Todas as operações de lista são puras e referencialmente transparentes. Mutação,
I/O e overhead de desempenho estão fora do escopo deste modelo.

### 14.3 Sem Paralelismo ou Avaliação Preguiçosa

Ao contrário de bibliotecas de streaming ou sequências preguiçosas, este modelo
é estritamente ansioso e sequencial, sem suporte a computação paralela ou
avaliação preguiçosa.

### 14.4 Limitações Impostas pela Ferramenta de Verificação Stainless

Devido a limitações atuais do verificador Scala Stainless (versão 0.9.8.8),
provas formais muitas vezes precisam depender de tipos numéricos concretos como
`BigInt`. O Stainless ainda não oferece suporte completo a abstrações numéricas
genéricas ou type classes como `Numeric[T]`, o que dificulta a verificação de
implementações parametrizadas por tipos numéricos arbitrários.

Como resultado, embora as propriedades matemáticas deste trabalho se apliquem
conceitualmente a qualquer domínio numérico que satisfaça as leis algébricas
exigidas, a verificação prática fica restrita a `BigInt`. Superar essas
limitações da ferramenta é uma direção importante para melhorias futuras,
permitindo maior generalidade e verificação formal mais flexível.

### 14.5 Escopo da Correção

Este artigo enfatiza a **correção matemática** de definições recursivas e
propriedades verificadas, em vez de comportamento em tempo de execução ou
eficiência em nível de sistema.

O uso de `BigInt` e de listas conceitualmente ilimitadas abstrai preocupações
como estouros de pilha, uso de memória e tempo de execução. Ele também contorna
limitações da versão atual do Scala Stainless em relação ao raciocínio numérico
genérico.

Embora limitem o uso prático em alguns contextos, essas hipóteses mantêm o foco
em provar correção funcional conforme definida por especificações recursivas.

Trabalhos futuros podem incluir o desenvolvimento de implementações alternativas
dessas estruturas de dados que tratem explicitamente restrições do mundo real,
como memória limitada e efeitos colaterais, junto com provas formais que
estabeleçam sua equivalência com o modelo atual, matematicamente rigoroso.

## 15. Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*.  
Proceedings of the ACM on Programming Languages, OOPSLA Issue. 

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Wikipedia contributors. (2026). *Formal verification*. Wikipedia.  
Disponível em: [https://en.wikipedia.org/wiki/Formal_verification](https://en.wikipedia.org/wiki/Formal_verification)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
The Rocq Development Team. *The Rocq Standard Library: Lists*.
Disponível em: [https://docs.rocq-prover.org/v8.16/stdlib/Coq.Lists.List.html](https://docs.rocq-prover.org/v8.16/stdlib/Coq.Lists.List.html)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
The Lean Community. *Mathlib: List Rotation*.
Disponível em: [https://leanprover-community.github.io/mathlib_docs/data/list/rotate.html](https://leanprover-community.github.io/mathlib_docs/data/list/rotate.html)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Division and Modulo from Recursive Normalization*.  
Disponível em: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009)

## Apêndice A: Código de Verificação Scala

### A.1 Deslocamento de Acesso pela Cauda — accessTailShiftRight

Fonte: [ListUtilsProperties.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala)

```scala
  def accessTailShiftRight[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
```

Fonte: [ListBoundUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala)

```scala
  def assertTailShiftLeft[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      assert( list == List(list.head) ++ list.tail )
      assert( list(position) == list.apply(position) )
      assert(assertTailShiftLeft(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds
```

### A.2 Identidade do Último Elemento — assertLastEqualsLastPosition

Fonte: [ListUtilsProperties.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala)

```scala
  def assertLastEqualsLastPosition[T](list: List[T]): Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      assert(list.head == list.last)
    } else {
      assert(assertLastEqualsLastPosition(list.tail))
      assertTailShiftLeft(list, list.size - 1)
      assert(list.last == list(list.size - 1))
    }
    list.last == list(list.size - 1)
  }.holds
```

### A.3 Fatia Recursiva pela Cauda — slice

Fonte: [ListUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala)

```scala
  def slice(list: List[BigInt], from: BigInt, to: BigInt): List[BigInt] = {
    require(from >= 0)
    require(to >= from)
    require(to < list.size)
    decreases(to)

    val current: BigInt = list(to)
    if (from == to) {
      List(current)
    } else {
      val prev = slice(list, from, to - 1)
      ListUtilsProperties.listAddValueTail(prev, current)
      prev ++ List(current)
    }
  }
```

### A.4 Fatia Recursiva pela Cabeça — headRecursiveSlice

Fonte: [SliceEquivalenceLemmas.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala)

```scala
def headRecursiveSlice[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), headRecursiveSlice(list, from + 1, to))
}
```

### A.5 Fatia por Intervalo de Índices — indexRangeValues

Fonte: [SliceEquivalenceLemmas.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala)

```scala
def indexRangeValues[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), indexRangeValues(list, from + 1, to))
}
```

### A.6 Consistência de Append da Fatia — assertAppendToSlice

Fonte: [ListUtilsProperties.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala)

```scala
  def assertAppendToSlice(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(from >= 0)
    require(from < to)
    require(to < list.size)
    
    listSumAddValue(list, list(to))
    
    ListUtils.slice(list, from, to) ==
      ListUtils.slice(list, from, to - 1) ++ List(list(to))
  }.holds
```

### A.7 Implementação da Soma — sum

Fonte: [ListUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala)

```scala
  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }
```

### A.8 Append à Esquerda Preserva Soma — listSumAddValue

Fonte: [ListUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala)

```scala
def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds
```

### A.9 Soma sobre Concatenação — listCombine

Fonte: [ListUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala)

```scala
  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(ListUtils.sum(listA) == BigInt(0))
      assert(ListUtils.sum(listB) == BigInt(0) + ListUtils.sum(listB))
      assert(ListUtils.sum(listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
      assert(listA ++ listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA ++ listB
      assert(bigList == List(listA.head) ++ listA.tail ++ listB)
      listSumAddValue(listA.tail ++ listB, listA.head)
    }
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB)
  }.holds
```

### A.10 Comutatividade da Soma — listSwap

Fonte: [ListUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListUtils.scala)

```scala
  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    assert(ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
    assert(ListUtils.sum(listB ++ listA) == ListUtils.sum(listB) + ListUtils.sum(listA))
    assert(ListUtils.sum(listA) + ListUtils.sum(listB) == ListUtils.sum(listB) + ListUtils.sum(listA))
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listB ++ listA)
  }.holds
```

### A.11 Produto Singleton — singletonProduct

Fonte: [ListProduct.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala)

```scala
  def singletonProduct(x: BigInt): Boolean = {
    product(List(x)) == x
  }.holds
```

### A.12 Extração de Elemento do Produto — productPullOutElement

Fonte: [ListProduct.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala)

```scala
  def productPullOutElement(
                             listA: List[BigInt],
                             e: BigInt,
                             listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      product(List(e) ++ listB) == e * product(listB)
    } else {
      productPullOutElement(listA.tail, e, listB)
      product(listA ++ List(e) ++ listB) ==
        e * product(listA ++ listB)
    }
  }.holds
```

### A.13 Produto sobre Concatenação — productConcatLemma

Fonte: [ListProduct.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala)

```scala
  def productConcatLemma(
                          listA: List[BigInt],
                          listB: List[BigInt]
                        ): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(product(listA) == BigInt(1))
      assert(product(listB) == product(listA) * product(listB))
      assert(listA ++ listB == listB)
    } else {
      productConcatLemma(listA.tail, listB)

      val concatenated = listA ++ listB

      assert(
        concatenated ==
          List(listA.head) ++ listA.tail ++ listB
      )

      assert(
        product(concatenated) ==
          listA.head * product(listA.tail ++ listB)
      )
    }

    product(listA ++ listB) ==
      product(listA) * product(listB)
  }.holds
```

### A.14 Comutatividade do Produto — productConcatCommutative

Fonte: [ListProduct.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala)

```scala
  def productConcatCommutative(
                                listA: List[BigInt],
                                listB: List[BigInt]
                              ): Boolean = {

    productConcatLemma(listA, listB)
    productConcatLemma(listB, listA)

    assert(
      product(listA ++ listB) ==
        product(listA) * product(listB)
    )

    assert(
      product(listB ++ listA) ==
        product(listB) * product(listA)
    )

    assert(
      product(listA) * product(listB) ==
        product(listB) * product(listA)
    )

    product(listA ++ listB) ==
      product(listB ++ listA)
  }.holds
```

### A.15 Produto Positivo — positiveProduct

Fonte: [ListProduct.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProduct.scala)

```scala
  def positiveProduct(elements: List[BigInt]): Boolean = {
    decreases(elements.size)

    require(ListBoundUtils.allGreaterThan(elements, 0))

    if (elements.isEmpty) {
      product(elements) > 0
    } else {
      positiveProduct(elements.tail)
      assert(product(elements.tail) > 0)
      product(elements) > 0
    }
  }.holds
```

### A.16 Cabeça Divide o Produto — ListProductDiv

Fonte: [ListProductDiv.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala)

```scala
  def ListProductDiv(
                          elements: List[BigInt]
                        ): Boolean = {

    require(elements.nonEmpty)
    require(ListBoundUtils.allGreaterThan(elements, 0))

    val p = elements.head
    val tailProduct = ListProduct.product(elements.tail)

    assert(
      ListProduct.product(elements) ==
        p * tailProduct
    )

    assert(ModIdentity.modIdentity(p))

    assert(
      ATimesBSameMod(
        BigInt(0),
        p,
        tailProduct
      )
    )

    Calc.mod(
      ListProduct.product(elements),
      p
    ) == BigInt(0)
  }.holds
```

### A.17 Todos os Elementos Dividem o Produto — allElementsDivideProduct

Fonte: [ListProductDiv.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala)

```scala
  def allElementsDivideProduct(
                                elements: List[BigInt]
                              ): Boolean = {

    require(ListBoundUtils.allGreaterThan(elements, 0))

    decreases(elements.size)

    if (elements.isEmpty) {
      true
    } else {

      val p = elements.head
      val tailProduct = ListProduct.product(elements.tail)

      assert(
        ListProduct.product(elements) ==
          p * tailProduct
      )

      assert(ModIdentity.modIdentity(p))

      assert(
        ATimesBSameMod(
          BigInt(0),
          p,
          tailProduct
        )
      )

      assert(
        Calc.mod(
          ListProduct.product(elements),
          p
        ) == BigInt(0)
      )

      allElementsDivideProduct(elements.tail)
    }
  }.holds
```

### A.18 Elemento Inserido Divide o Produto — insertedElementDividesProduct

Fonte: [ListProductDiv.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala)

```scala
  def insertedElementDividesProduct(
                                     prefix: List[BigInt],
                                     e: BigInt,
                                     suffix: List[BigInt]
                                   ): Boolean = {

    require(e > 0)
    require(ListBoundUtils.allGreaterThan(prefix, 0))
    require(ListBoundUtils.allGreaterThan(suffix, 0))

    ListProduct.productPullOutElement(
      prefix,
      e,
      suffix
    )

    assert(
      ListProduct.product(
        prefix ++ List(e) ++ suffix
      ) ==
        e * ListProduct.product(
          prefix ++ suffix
        )
    )

    assert(ModIdentity.modIdentity(e))

    assert(
      ATimesBSameMod(
        BigInt(0),
        e,
        ListProduct.product(prefix ++ suffix)
      )
    )

    Calc.mod(
      ListProduct.product(
        prefix ++ List(e) ++ suffix
      ),
      e
    ) == BigInt(0)
  }.holds
```

### A.19 Todos Maiores que no Índice — assertGreaterThanAtIndex

Fonte: [ListBoundUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala)

```scala
  def assertGreaterThanAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(pos >= 0 && pos < list.size)
    decreases(pos)
    if (pos == BigInt(0)) {
      list.head > value
    } else {
      assert(assertGreaterThanAtIndex(list.tail, value, pos - 1))
      assert(assertTailShiftLeft(list, pos))
      list(pos) > value
    }
  }.holds
```

### A.20 Append Preserva Todos Maiores que — assertAppendGreaterThan

Fonte: [ListBoundUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala)

```scala
  def assertAppendGreaterThan(listA: List[BigInt], listB: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(listA, value))
    require(allGreaterThan(listB, value))
    decreases(listA.size)
    if (listA.isEmpty) {
      allGreaterThan(listA ++ listB, value)
    } else {
      assert(assertAppendGreaterThan(listA.tail, listB, value))
      assert(allGreaterThan(listA.tail ++ listB, value))
      assert(listA.head > value)
      allGreaterThan(listA ++ listB, value)
    }
  }.holds
```

### A.21 Todos Maiores que na Cabeça e na Cauda — assertGreaterThanHeadTail

Fonte: [ListBoundUtils.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/ListBoundUtils.scala)

```scala
  def assertGreaterThanHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(list.nonEmpty)
    list.head > value && allGreaterThan(list.tail, value)
  }.holds
```

### A.22 Checar Todos Maiores no Índice — checkAllBiggerThanValueAtIndex

Fonte: [ListUtilsProperties.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala)

```scala
  def checkAllBiggerThanValueAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(pos >= 0 && pos < list.size)
    ListBoundUtils.assertGreaterThanAtIndex(list, value, pos)
  }.holds
```

### A.23 Checar Todos Maiores na Cabeça e na Cauda — checkAllBiggerThanValueHeadTail

Fonte: [ListUtilsProperties.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala)

```scala
  def checkAllBiggerThanValueHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(list.nonEmpty)
    ListBoundUtils.assertGreaterThanHeadTail(list, value)
  }.holds
```

### A.24 Equivalência de Fatias — tailHeadAndIndexRangeSlicesAreEqual

Fonte: [SliceEquivalenceLemmas.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala)

```scala
  def tailHeadAndIndexRangeSlicesAreEqual(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)

    val indexSlice = indexRangeValues(list, from, to)
    val tailSlice = ListUtils.slice(list, from, to)
    val headSlice = headRecursiveSlice(list, from, to)

    if (from == to) {
      assert(indexSlice == List(list(from)))
      assert(tailSlice == List(list(from)))
      assert(headSlice == List(list(from)))
    } else {
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from, to - 1))
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from + 1, to))
      val reconstructedTail = ListUtils.slice(list, from, to - 1) ++ List(list(to))
      assert(tailSlice == reconstructedTail)
      assert(tailSlice == indexSlice)
      assert(headSlice == indexSlice)
      assert(tailSlice == headSlice)
    }
    (
      tailSlice == headSlice &&
      tailSlice == indexSlice &&
      headSlice == indexSlice
    )
  }.holds
```

## Apêndice B: Saída do Log de Verificação Stainless

A execução mais recente de `just verify` verifica todas as propriedades
descritas sem erros. A saída completa do log está disponível em:
[logs/verify-ch-3-v1-chapter3-_.log](https://github.com/thiagomata/prime-numbers/blob/list-article-v1.0.2/logs/verify-ch-3-v1-chapter3-_.log)
