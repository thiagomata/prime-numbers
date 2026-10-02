# Verificação Formal dos Estágios da Sequência de Peneira e Suas Transições

**Autor:** Thiago Henrique Ramos da Mata
Pesquisador Independente
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)<br>
**DOI:** [10.5281/zenodo.22955782](https://doi.org/10.5281/zenodo.22955782)

## Resumo

<div align="justify">
<p style="text-align: justify">

Este artigo define um estágio da sequência de peneira como a sequência
crescente de inteiros aceitos por um prefixo finito dos filtros primos. O padrão
aceito é periódico módulo o produto desses filtros, então uma lista finita de
lacunas positivas reconstrói todo o estágio infinito. Verificamos formalmente o
crescimento estrito, a completude, o deslocamento por bloco de período, a
reconstrução do ciclo de lacunas e a contagem exata de transição do estágio. Se
a cabeça atual é $h$, o período atual tem $T$ valores aceitos e o módulo atual é
$M$, então a janela expandida de comprimento $hM$ contém $hT$ sobreviventes
antigos; exatamente $T$ são múltiplos de $h$, deixando $T(h-1)$ sobreviventes.
Também verificamos a regra local de copiar-ou-mesclar para as próximas lacunas.
Para cada lacuna 2 linear real, os dois ataques aos extremos ocorrem em
deslocamentos de levantamento distintos, então exatamente dois de seus $h$
levantamentos são destruídos e exatamente $h-2$ mantêm ambos os extremos. Sob
pré-condições estruturais e de período explícitas, o prefixo de lacunas
resultante concorda com a próxima especificação linear.

O resultado formal tem duas fronteiras explícitas. Primeiro, a primalidade da
próxima cabeça é condicional ao limite quadrático fornecido matematicamente pelo
postulado de Bertrand. Segundo, o artigo prova a transição semântica entre
estágios, enquanto a construção direta do próximo ciclo a partir de um ciclo
atual repetido e filtrado é um problema aberto de composição separado. Portanto,
o artigo estabelece uma especificação de peneira em estágio finito e uma
semântica de transição formalmente verificadas, não um novo algoritmo de
peneiramento de primos nem um teorema sobre a persistência de alguma lacuna
prima particular em uma janela curta prescrita.

</p>
</div>

<a id="1-introduction"></a>

## 1. Introdução

A peneira de Eratóstenes remove repetidamente múltiplos de primos conhecidos
[[5]](#ref5). Uma implementação padrão armazena um vetor limitado e risca
compostos. A Sequência de Peneira estudada aqui expõe uma visão matemática
diferente: depois que um conjunto finito de filtros primos foi instalado, os
sobreviventes formam uma sequência periódica infinita. Um ciclo finito de
lacunas adjacentes, portanto, representa todo o estágio.

Essa representação pertence à ampla família de descrições de peneiras cíclicas
ou baseadas em rodas. A revisão de Pritchard coloca peneiras de roda entre as
famílias sistemáticas de peneiras de números primos [[6]](#ref6). A contribuição
presente não é a ideia de roda em si. Ela é a decomposição explícita do estágio
e da transição em contratos que podem ser checados pelo Stainless, um verificador
para programas Scala [[7]](#ref7), contra uma biblioteca de aritmética e listas
de primeiros princípios.

A prova é organizada nestes grupos de propriedades:

- semântica de estágio e enumeração crescente completa - [§3](#3-linear-stage-semantics);
- período canônico e reconstrução por ciclo finito de lacunas - [§4](#4-period-and-cycle-reconstruction);
- invariância de ciclo repetido, filtragem exata e dinâmica de copiar-ou-mesclar - [§5](#5-installing-the-current-head-as-a-filter);
- primalidade da próxima cabeça e concordância do próximo estágio - [§6](#6-the-next-stage);
- hipóteses condicionais e problemas abertos de composição - [§7](#7-exact-proof-boundary).

O objeto matemático é separado de seus namespaces de prova. `SpecSieveSequence`
é o modelo de dados e a especificação semântica linear. Objetos independentes de
propriedades estabelecem os teoremas de período, contagem de sobreviventes,
transição, montagem do próximo estágio e primalidade da cabeça.

<a id="2-preliminaries"></a>

## 2. Preliminares

Esta seção fixa a notação, relaciona as visões linear e cíclica, e declara como
interpretar um contrato verificado em Stainless.

- [§2.1](#21-stage-definition) define um estágio e seu predicado de aceitação.
- [§2.2](#22-period-and-gap-cycle) define o período finito e o ciclo de lacunas.
- [§2.3](#23-source-evidence-map) mapeia a arquitetura da prova.
- [§2.4](#24-verification-evidence) explica a fronteira da verificação.

<a id="21-stage-definition"></a>

### 2.1 Definição de Estágio

Seja um estágio $S$ determinado por uma cabeça prima atual $h$ e pela lista
completa $\overline{P}$ dos primos menores que $h$. A lista é armazenada em
ordem decrescente, mas sua ordem não afeta a divisibilidade. Defina

```math
\begin{aligned}
M &= \prod_{q \in \overline{P}} q,
  &&\text{[Primorial da cauda]} \\
A_S(v) &\Longleftrightarrow
  v \ge h \land
  \forall q \in \overline{P},\ v \not\equiv 0 \pmod q.
  &&\text{[Aceitação]}
\end{aligned}
```

A sequência linear $L=(\ell_k)_{k\ge 0}$ começa em $h$ e seleciona
repetidamente o menor valor aceito posterior:

```math
\begin{aligned}
\ell_0 &= h, \\
\ell_{k+1}
  &= \min\{v\gt\ell_k : A_S(v)\}.
\end{aligned}
```

Um estágio **não** afirma que todo $\ell_k$ é primo. Por exemplo, o estágio com
$h=5$ e filtros $3,2$ emite $5,7,11,13,17,19,23,25,\ldots$. O valor $25$
sobrevive porque a cabeça atual $5$ ainda não foi adicionada à lista de filtros.
A geração de primos vem da cadeia de cabeças de estágio, não de tratar todos os
valores em um estágio como primos.

A figura abaixo torna isso concreto para seis estágios iniciais: cada painel é
composto pelos primeiros $100$ valores de um sobrevivente remodelados em uma
grade $10\times10$, coloridos de verde onde o sobrevivente é de fato primo e de
vermelho onde o conjunto atual de filtros o aceitou mesmo sendo composto (o
estágio $0$, ainda sem filtro instalado, marca todo inteiro composto dessa
forma). Toda célula vermelha é exatamente o fenômeno nomeado acima — um valor
que $A_S$ aceita atualmente e que uma cabeça de estágio posterior removerá.

![Seis pequenas matrizes de acerto/erro, uma por estágio inicial: células verdes são sobreviventes que são de fato primos, células vermelhas são sobreviventes que o conjunto atual de filtros aceita apesar de serem compostos](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/hit-miss-matrices.svg)

<a id="22-period-and-gap-cycle"></a>

### 2.2 Período e Ciclo de Lacunas

Como todo $q\in\overline{P}$ divide $M$, a aceitação não muda ao adicionar $M$
dentro do domínio do estágio $v\ge h$:

```math
\begin{aligned}
A_S(v+M)
&\Longleftrightarrow
(v+M)\ge h\ \land\
\forall q\in\overline{P},\ (v+M)\not\equiv0\pmod q \\
&\Longleftrightarrow
v\ge h\ \land\
\forall q\in\overline{P},\ v\not\equiv0\pmod q \\
&\Longleftrightarrow A_S(v).
\end{aligned}
```

Seja $T\gt0$ o índice único que satisfaz $\ell_T=h+M$. Defina uma lista
completa de lacunas

```math
\begin{aligned}
G &= (g_0,\ldots,g_{T-1}), \\
g_i &= \ell_{i+1}-\ell_i.
\end{aligned}
```

Toda lacuna é positiva e as lacunas telescopam ao longo do período:

```math
\begin{aligned}
g_i &\gt 0, \\
\sum_{i=0}^{T-1} g_i
  &= \ell_T-\ell_0 \\
  &= (h+M)-h \\
  &= M.
\end{aligned}
```

A integral do ciclo adiciona repetidamente as entradas de $G$. Com a indexação
usada pela implementação Scala, sua posição $k-1$ reconstrói $\ell_k$ para todo
$k\gt0$.

<a id="23-source-evidence-map"></a>

### 2.3 Mapa de Evidência de Fonte

As provas abaixo usam `SpecSieveSequence` como o modelo matemático linear de um
estágio. Objetos de propriedades separados verificam os fatos de período,
reconstrução do ciclo de lacunas, contagem de sobreviventes, transição de
copiar-ou-mesclar, concordância do próximo estágio e primalidade da cabeça. O
modelo não depende desses objetos de propriedades; eles são evidência apoiada em
fonte para as propriedades matemáticas declaradas no artigo.

A construção se apoia nas bases verificadas de módulo [[1]](#ref1), listas
[[2]](#ref2), ciclos [[3]](#ref3) e integral de ciclo [[4]](#ref4).

<a id="24-verification-evidence"></a>

### 2.4 Evidência de Verificação

Cada propriedade verificada citada abaixo está vinculada a um contrato Scala
concreto no repositório. As pré-condições nesses contratos fazem parte da
declaração do teorema, e o artigo as declara em forma matemática antes de criar
link para a fonte. Isso mantém o resultado matemático e a evidência em
Stainless alinhados sem depender dos totais de condições de verificação do
repositório inteiro, que mudam quando funções não relacionadas são adicionadas.
As bases formais da estrutura de verificação são descritas em [[8]](#ref8).

<a id="3-linear-stage-semantics"></a>

## 3. Semântica Linear do Estágio

A especificação linear é uma enumeração ordenada exatamente dos inteiros que
passam pelos filtros instalados na cabeça ou após ela.

- `apply` retorna valores aceitos e nunca anda para trás.
- `indexOfAccepted` prova a completude da enumeração.
- o crescimento estrito torna índices e lacunas adjacentes inequívocos.

<a id="31-accepted-values-and-completeness"></a>

### 3.1 Valores Aceitos e Completude

O contrato `apply` do gerador prova a correção:
$A_S(\ell_k)$ para todo $k\ge0$. Reciprocamente, `indexOfAccepted` prova que
todo $v\ge h$ aceito ocorre em algum índice. Juntos, eles estabelecem enumeração
exata, não apenas a geração de um subconjunto.

```math
\begin{aligned}
\forall k\ge0,\quad
A_S(\ell_k)
&\quad\text{[Correção]} \\
\forall v\ge h,\quad
A_S(v)
&\Longrightarrow
\exists i\ge0,\ \ell_i=v
\quad\text{[Completude]}.
\end{aligned}
```

Para a completude, comece em $\ell_0=h\le v$. Se o valor gerado atual é menor
que $v$, o próximo valor aceito gerado não pode passar por cima de $v$, porque
$v$ em si é aceito. Repetir essa descida finita em $v-\ell_k$ alcança um índice
$i$ com $\ell_i=v$.

Este contrato verificado é implementado em [
  SpecSieveSequence::indexOfAccepted
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/SpecSieveSequence.scala).

<a id="32-strict-increase"></a>

### 3.2 Crescimento Estrito

Cada passo recursivo busca estritamente após o resultado anterior.
Consequentemente, a sequência é estritamente crescente, os índices são
injetivos e toda lacuna adjacente é positiva.

```math
\begin{aligned}
\ell_{k+1}
&\ge \ell_k+1
  &&\text{[A busca começa após o valor anterior]} \\
&\gt \ell_k
  &&\text{[Ordem inteira]} \\
g_k
&=\ell_{k+1}-\ell_k\gt0
  &&\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSequence::applyStrictlyIncreases
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/SpecSieveSequence.scala).

<a id="4-period-and-cycle-reconstruction"></a>

## 4. Período e Reconstrução do Ciclo

A representação finita funciona porque o predicado de filtro é periódico e a
varredura preserva a ordem dos resíduos aceitos repetidos.

- um período desloca todo valor gerado por $M$;
- todo bloco posterior é uma cópia transladada do primeiro bloco;
- integrar um ciclo finito positivo de lacunas reconstrói a varredura infinita.

<a id="41-canonical-block-shift"></a>

### 4.1 Deslocamento Canônico de Bloco

A fronteira $h+M$ passa exatamente pelos mesmos filtros que $h$, então a
completude dá um índice positivo $T$ com $\ell_T=h+M$. A periodicidade da
aceitação e a ordem estrita então identificam o $k$-ésimo valor aceito no bloco
seguinte:

```math
\begin{aligned}
A_S(v+M) &= A_S(v)
  &&\text{[Invariância por período modular]} \\
\ell_T &= h+M
  &&\text{[Fronteira canônica]} \\
\ell_{k+T} &= \ell_k+M
  &&\text{[Mesmo sobrevivente ordenado]} \\
\ell_{k+nT} &= \ell_k+nM
  &&\text{[Indução em blocos]}\quad\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqPeriodProperties::assertBlockShiftMultiple
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqPeriodProperties.scala).

<a id="42-gap-cycle-reconstruction"></a>

### 4.2 Reconstrução pelo Ciclo de Lacunas

Seja `GapCycle(G)` o armazenamento das primeiras $T$ diferenças adjacentes. O
teorema de deslocamento por bloco torna essas diferenças periódicas:

```math
\begin{aligned}
g_{k+T}
&=\ell_{k+T+1}-\ell_{k+T} \\
&=(\ell_{k+1}+M)-(\ell_k+M)
  &&\text{[Deslocamento por bloco]} \\
&=g_k.
\end{aligned}
```

A integral do ciclo começa em $h$ e adiciona essas lacunas. A indução em $k$
então reconstrói todo valor da varredura:

```math
\begin{aligned}
I_G(0)
&=h+g_0=\ell_1
  &&\text{[Base]} \\
I_G(k)
&=I_G(k-1)+g_k \\
&=\ell_k+(\ell_{k+1}-\ell_k)
  &&\text{[Hipótese de indução]} \\
&=\ell_{k+1}
  &&\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqPeriodProperties::assertSpecGapCycleIntegralMatchesApply
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqPeriodProperties.scala).

<a id="43-repetition-does-not-change-the-infinite-sequence"></a>

### 4.3 A Repetição Não Muda a Sequência Infinita

A transição prepara $h$ cópias do período atual antes de instalar a cabeça $h$
como novo filtro. Repetir a lista armazenada de lacunas multiplica o período da
representação finita de $T$ para $hT$, mas não muda a sequência periódica
infinita representada pela integral do ciclo.

```math
\begin{aligned}
G^{\langle h\rangle}
  &=\underbrace{G\mathbin{\texttt{++}}\cdots\mathbin{\texttt{++}}G}_{h\text{ cópias}}, \\
|G^{\langle h\rangle}|&=hT, \\
G^{\langle h\rangle}_{k\bmod hT}
  &=G_{k\bmod T}, \\
I_{G^{\langle h\rangle}}(k)
  &=I_G(k)
  \quad\text{[Incrementos e valor inicial iguais]}\quad\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecDerivedRepeatedCycleProperties::assertSpecRepeatedCycleIntegralMatchesBase
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecDerivedRepeatedCycleProperties.scala).

<a id="5-installing-the-current-head-as-a-filter"></a>

## 5. Instalando a Cabeça Atual como Filtro

O próximo estágio adiciona $h$ à lista de filtros ativos. Sobre uma janela
expandida completa, essa operação tem uma contagem exata e um efeito
determinístico sobre as lacunas.

- o estágio antigo expandido contém exatamente $hT$ valores aceitos;
- exatamente $T$ desses valores são divisíveis por $h$;
- uma lacuna 2 linear real tem exatamente dois levantamentos destruídos e
  $h-2$ levantamentos cujos extremos sobrevivem;
- toda próxima lacuna ou é copiada ou é uma soma de lacunas antigas
  consecutivas;
- filtrar as visões de ciclo base e ciclo repetido produz listas iguais de
  lacunas entre sobreviventes.

<a id="51-exact-survivor-count"></a>

### 5.1 Contagem Exata de Sobreviventes

Considere os valores aceitos com índices $r+iT$, onde $0\le r\lt T$ e
$0\le i\lt h$. O teorema de deslocamento por bloco dá

```math
\begin{aligned}
\ell_{r+iT}=\ell_r+iM.
\end{aligned}
```

A cabeça $h$ é um primo não presente entre os fatores primos menores de $M$,
então $\gcd(M,h)=1$. A multiplicação por $M$ permuta os resíduos módulo $h$.
Para cada $r$ fixo, exatamente um deslocamento $i\in\{0,\ldots,h-1\}$ portanto
satisfaz $\ell_r+iM\equiv0\pmod h$. Há $T$ escolhas de $r$, então exatamente
$T$ sobreviventes antigos são removidos:

```math
\begin{aligned}
N_{\mathrm{old}} &= hT
  &&\text{[Blocos repetidos]} \\
N_{\mathrm{removed}} &= T
  &&\text{[Um resíduo zero por linha]} \\
N_{\mathrm{survive}}
  &=hT-T \\
  &=T(h-1)
  &&\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Este é um teorema exato de período completo, não uma estimativa probabilística
de densidade.

Esta propriedade é verificada em [
  SpecSieveSeqSurvivorCountProperties::assertSameHeadExtendedFilterCount
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqSurvivorCountProperties.scala).

<a id="52-exact-lifted-copy-law-for-a-real-2-gap"></a>

### 5.2 Lei Exata de Cópias Levantadas para uma Lacuna 2 Real

Esta subseção diz respeito à sequência de peneira determinística real, não a um
modelo aleatório. Suponha que dois valores consecutivos na sequência real
satisfaçam $\ell_{k+1}-\ell_k=2$. Escreva $p=h$ para o primo ímpar entrante e
$M$ para o primorial da cauda atual. O bloco completo de levantamento contém os
$p$ pares de extremos

```math
(\ell_k+jM,\ \ell_{k+1}+jM),
\qquad 0\le j\lt p.
```

O resultado verificado é deliberadamente local a um par real da sequência. Ele
ainda não agrega sobre a lacuna de volta cíclica nem estabelece uma recorrência
para a população total de lacunas 2 do próximo estágio.

<a id="521-the-two-forbidden-lift-offsets-are-distinct"></a>

#### 5.2.1 Os Dois Deslocamentos de Levantamento Proibidos São Distintos

Cada extremo tem um único deslocamento de levantamento no qual o primo entrante
o divide. Esses deslocamentos não podem coincidir: se o mesmo primo dividisse
ambos os extremos levantados, dividiria sua diferença $2$, o que é impossível
para um primo ímpar. Esse é o fato estrutural que impede que os dois ataques aos
extremos colapsem em uma única cópia destruída.

```math
\begin{aligned}
j_L,j_R&\in\{0,\ldots,p-1\},
&&[\text{Por Deslocamento de Levantamento Único}]\\
\ell_k+j_LM&\equiv0\pmod p,\\
\ell_{k+1}+j_RM&\equiv0\pmod p.\\[2pt]
j_L=j_R=j
&\Longrightarrow
(\ell_{k+1}+jM)-(\ell_k+jM)\equiv0\pmod p
&&[\text{Substituição}]\\
&\Longrightarrow 2\equiv0\pmod p
&&[\ell_{k+1}-\ell_k=2]\\
&\Longrightarrow 2=0
&&[\text{Por Propriedade Modular},\ 2\lt p],
\end{aligned}
```

o que é uma contradição. Portanto

```math
j_L\ne j_R.
\qquad\blacksquare\ \text{[C.Q.D.]}
```

```scala
def assertForbiddenLiftOffsetsDistinct(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)
  val right = seq.apply(k + BigInt(1))
  val leftOffset = BezoutUtils.coprimeStepZeroOffset(left, step, p)
  val rightOffset = BezoutUtils.coprimeStepZeroOffset(right, step, p)

  assert(right == left + BigInt(2))
  assert(Calc.mod(left + leftOffset * step, p) == BigInt(0))
  assert(Calc.mod(right + rightOffset * step, p) == BigInt(0))

  if (leftOffset == rightOffset) {
    val leftCopy = left + leftOffset * step
    val rightCopy = right + rightOffset * step
    assert(rightCopy == leftCopy + BigInt(2))
    assert(Calc.mod(leftCopy, p) == BigInt(0))
    assert(Calc.mod(rightCopy, p) == BigInt(0))
    assert(ModOperations.modZeroPlusC(leftCopy, p, BigInt(2)))
    assert(Calc.mod(rightCopy, p) == Calc.mod(BigInt(2), p))
    assert(ModSmallDividend.modSmallDividend(BigInt(2), p))
    assert(Calc.mod(BigInt(2), p) == BigInt(2))
    assert(Calc.mod(rightCopy, p) != BigInt(0))
    leftOffset != rightOffset
  } else {
    leftOffset != rightOffset
  }
}.holds
```

Esta propriedade é verificada em [
  SpecSieveSeqTwoGapProperties::assertForbiddenLiftOffsetsDistinct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

<a id="522-exactly-two-lifted-copies-are-destroyed"></a>

#### 5.2.2 Exatamente Duas Cópias Levantadas São Destruídas

Um par copiado é destruído quando pelo menos um extremo é divisível por $p$. O
extremo esquerdo é atacado uma vez, o extremo direito é atacado uma vez, e o
teorema de deslocamentos distintos torna esses dois conjuntos unitários de
ataques disjuntos. Consequentemente, sua união contém exatamente dois índices de
cópia.

```math
\begin{aligned}
D_L&=\{j:0\le j\lt p,\ p\mid(\ell_k+jM)\},\\
D_R&=\{j:0\le j\lt p,\ p\mid(\ell_{k+1}+jM)\},
&&[\text{Pela Definição}]\\
|D_L|&=1,
\qquad |D_R|=1,
&&[\text{Por Deslocamento de Levantamento Único}]\\
D_L\cap D_R&=\varnothing
&&[\text{Pelo Lema }j_L\ne j_R]\\
D&=D_L\cup D_R,
&&[\text{Pela Definição}]\\
|D|&=|D_L|+|D_R|=2.
&&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

```scala
def assertExactlyTwoDestroyedCopies(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)
  val right = seq.apply(k + BigInt(1))
  val leftWitness = BezoutUtils.coprimeStepZeroOffset(left, step, p)
  val rightWitness = BezoutUtils.coprimeStepZeroOffset(right, step, p)

  assert(right == left + BigInt(2))
  assert(assertForbiddenLiftOffsetsDistinct(seq, k))
  assert(leftWitness != rightWitness)
  assert(assertDestroyedCountEqualsEndpointCounts(
    left,
    step,
    p,
    BigInt(0),
    leftWitness,
    rightWitness
  ))
  assert(SieveUtils.assertCountZeroOffsetsOne(left, step, p))
  assert(SieveUtils.countZeroOffsets(left, step, p, BigInt(0)) == BigInt(1))
  assert(SieveUtils.assertCountZeroOffsetsOne(right, step, p))
  assert(SieveUtils.countZeroOffsets(right, step, p, BigInt(0)) == BigInt(1))

  countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == BigInt(2)
}.holds
```

Esta propriedade é verificada em [
  SpecSieveSeqTwoGapProperties::assertExactlyTwoDestroyedCopies
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

<a id="523-exactly-p-2-lifted-copies-keep-both-endpoints"></a>

#### 5.2.3 Exatamente \(p-2\) Cópias Levantadas Mantêm Ambos os Extremos

Há $p$ levantamentos candidatos no bloco completo. Remover os dois, e apenas
dois, índices destruídos deixa exatamente $p-2$ cópias cujos dois extremos
sobrevivem ao filtro entrante. Esta é uma contagem determinística exata, não um
valor esperado nem uma heurística de independência.

```math
\begin{aligned}
|\{0,\ldots,p-1\}|&=p,
&&[\text{Pela Definição}]\\
|D|&=2,
&&[\text{Pelo Lema: Exatamente Duas Cópias Destruídas}]\\
N_{\mathrm{endpoint\text{-}surviving}}
&=p-|D|\\
&=p-2.
&&\text{[Substituição]}\quad\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

```scala
def assertExactlyHeadMinusTwoCopiesSurvive(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)

  assert(assertExactlyTwoDestroyedCopies(seq, k))
  p - countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == p - BigInt(2)
}.holds
```

Esta propriedade é verificada em [
  SpecSieveSeqTwoGapProperties::assertExactlyHeadMinusTwoCopiesSurvive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

<a id="53-copy-or-merge-gap-dynamics"></a>

### 5.3 Dinâmica de Lacunas por Copiar-ou-Mesclar

Sejam $\ell_k\lt\ell_{k+1}$ valores antigos consecutivos. Se ambos sobrevivem
ao novo filtro, nenhum novo valor aceito pode aparecer entre eles, então sua
diferença é copiada sem mudança. Se um ou mais valores antigos são removidos, os
próximos extremos sobreviventes são $\ell_k$ e $\ell_j$ para algum
$j\gt k+1$; o telescopamento mescla as lacunas intermediárias:

```math
\begin{aligned}
\ell_{k+1}\text{ sobrevive}
&\Longrightarrow
g'_m=\ell_{k+1}-\ell_k=g_k,
  &&\text{[Cópia]} \\
\ell_{k+1},\ldots,\ell_{j-1}\text{ removidos}
&\Longrightarrow
g'_m=\ell_j-\ell_k \\
&=\sum_{i=k}^{j-1}(\ell_{i+1}-\ell_i) \\
&=\sum_{i=k}^{j-1}g_i.
  &&\text{[Mesclagem]}\quad\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

O ramo de sobrevivente imediato é verificado em [
  SpecSieveSeqNextProperties::assertFilterPreservesNextGap
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

O ramo de sucessor pulado é verificado como teorema de apoio. Quando o sucessor
antigo imediato é removido, a próxima lacuna é a soma das lacunas antigas até o
primeiro sobrevivente posterior. Esta propriedade de apoio é verificada em [
  SpecSieveSeqNextProperties::assertMergeGapEqualsOldGapSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

O prefixo mesclado geral é então verificado contra a lista de lacunas da próxima
especificação. Esta propriedade é verificada em [
  SpecSieveSeqNextProperties::assertMergedGapPrefixMatchesNext
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

<a id="54-filtering-the-repeated-cycle-preserves-the-semantic-result"></a>

### 5.4 Filtrar o Ciclo Repetido Preserva o Resultado Semântico

[§4.3](#43-repetition-does-not-change-the-infinite-sequence) provou igualdade pontual entre as integrais do ciclo base e do ciclo
repetido. Aplicar o mesmo predicado de divisibilidade nas mesmas posições deve,
portanto, selecionar valores sobreviventes idênticos. Listas iguais de
sobreviventes têm listas iguais de lacunas adjacentes:

```math
\begin{aligned}
I_{G^{\langle h\rangle}}(k)&=I_G(k)
  &&\text{[Igualdade do ciclo repetido]} \\
I_{G^{\langle h\rangle}}(k)\not\equiv0\pmod h
&\Longleftrightarrow I_G(k)\not\equiv0\pmod h
  &&\text{[Substituição]} \\
\text{survivors}(I_{G^{\langle h\rangle}},h)
&=\text{survivors}(I_G,h) \\
\text{gaps}(\text{survivors}(I_{G^{\langle h\rangle}},h))
&=\text{gaps}(\text{survivors}(I_G,h))
  &&\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecDerivedRepeatedCycleProperties::assertSpecBaseAndRepeatedGapListMatch
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecDerivedRepeatedCycleProperties.scala).

<a id="6-the-next-stage"></a>

## 6. O Próximo Estágio

O próximo estágio instala a cabeça atual como filtro, começa no primo seguinte e
representa sua própria sequência aceita por um novo ciclo finito de lacunas. Ao
longo desta seção, um apóstrofo marca a versão própria do próximo estágio de cada
objeto definido em [§2](#2-preliminaries): $S'$ é o próximo estágio,
$h'=\ell_1$ sua cabeça, $M'$ seu primorial de cauda, $\ell'$ sua enumeração
linear, e $G'$ seu ciclo de lacunas.

- o primeiro sucessor do estágio antigo é o próximo primo sob o limite
  quadrático;
- o prefixo semântico de lacunas mescladas é igual ao prefixo de lacunas da
  próxima especificação;
- uma fronteira válida do próximo período permite que o próximo ciclo de lacunas
  reconstrua a próxima varredura.

<a id="61-square-bound-successor-primality"></a>

### 6.1 Primalidade do Sucessor pelo Limite Quadrático

O primeiro sucessor do estágio antigo é aceito por todos os filtros menores que
$h$. Se esse sucessor está abaixo de $h^2$, então um sucessor composto teria um
divisor primo abaixo de $h$, contradizendo a aceitação. Portanto, o sucessor é
primo sob a pré-condição do limite quadrático:

```math
\begin{aligned}
\ell_1&\lt h^2, \\
\ell_1\text{ composto}
&\Longrightarrow
\exists d\lt h,\ d\text{ primo e }d\mid \ell_1
  &&\text{[Menor divisor primo]} \\
d\lt h
&\Longrightarrow d\in\overline{P}
  &&\text{[Todos os primos menores são filtros]} \\
d\mid\ell_1
&\Longrightarrow \neg A_S(\ell_1)
  &&\text{[Contradição com o filtro]} \\
&\Longrightarrow \ell_1\text{ é primo}.
  &&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqHeadIsPrime::assertApplyOneIsPrimeIfBelowHeadSq
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala).

<a id="62-the-first-successor-is-the-next-prime"></a>

### 6.2 O Primeiro Sucessor é o Próximo Primo

Suponha que o próximo primo depois de $h$ seja $p^+$ e que $p^+\lt h^2$. O
próximo primo passa por todo filtro de primo menor, então $\ell_1\le p^+$.
Reciprocamente, se $\ell_1\lt h^2$ fosse composto, teria um divisor primo no
máximo $\sqrt{\ell_1}\lt h$. Esse divisor pertence a $\overline{P}$,
contradizendo a aceitação. Assim, $\ell_1$ é primo. Nenhum primo fica
estritamente entre $h$ e $p^+$, então $\ell_1=p^+$.

```math
\begin{aligned}
A_S(p^+) &\quad\text{[Primo maior distinto passa pelos filtros antigos]} \\
\ell_1 &\le p^+
  &&\text{[Menor sucessor aceito]} \\
\ell_1 \lt h^2
  &\Longrightarrow \ell_1\text{ é primo}
  &&\text{[Pequeno divisor composto]} \\
h\lt\ell_1\le p^+,
\quad \ell_1\text{ primo}
  &\Longrightarrow \ell_1=p^+
  &&\text{[Nenhum primo intermediário]}\quad\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqHeadIsPrime::assertApplyOneEqualsNextPrime
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala).

<a id="63-semantic-pipeline-agreement"></a>

### 6.3 Concordância Semântica do Pipeline

Seja $T'=T(h-1)$. Sob as invariantes declaradas de relação entre estágios, o
processo semântico de mesclagem começa no primeiro valor antigo sobrevivente e
emite $T'$ lacunas mescladas. [§5.3](#53-copy-or-merge-gap-dynamics) fornece a
indução por copiar-ou-mesclar usada para provar que essa lista é igual às
primeiras $T'$ lacunas da próxima especificação linear:

```math
\begin{aligned}
T'&=T(h-1), \\
\text{mergedGaps}(S,S',1,T')
&=\text{gapList}(S',0,T')
  \quad\text{[Por indução de copiar-ou-mesclar]}\quad\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqNextStageProperties::assertPipelineOutputMatchesNextGapList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextStageProperties.scala).

<a id="64-conditional-next-cycle-reconstruction"></a>

### 6.4 Reconstrução Condicional do Próximo Ciclo

Se $T'$ é conhecido como o período canônico do próximo estágio, o teorema
genérico de reconstrução do ciclo de [§4.2](#42-gap-cycle-reconstruction) se
aplica diretamente a esse estágio:

```math
\begin{aligned}
\ell'_{T'} &= h'+M'
  &&\text{[Fronteira do próximo período]} \\
G'&=\text{gapList}(S',0,T') \\
I_{G'}(k-1)&=\ell'_k
  &&\text{[Reconstrução do ciclo]}\quad\blacksquare\ \text{[C.Q.D.]}.
\end{aligned}
```

Esta propriedade é verificada em [
  SpecSieveSeqNextStageProperties::assertNextCycleReconstructsNextSpec
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextStageProperties.scala).

<a id="7-exact-proof-boundary"></a>

## 7. Fronteira Exata da Prova

Os resultados verificados acima não formam um teorema operacional
incondicional. Esta seção declara a fronteira como parte do teorema.

- **Limite quadrático.** `SpecSieveSequence.next` e o teorema da próxima cabeça
  exigem $p^+\lt h^2$. O postulado de Bertrand fornece um primo entre $h$ e
  $2h$; para primo $h\ge2$, isso implica o limite quadrático exigido (com
  $h=2$ checado diretamente). Ramanujan dá uma prova direta do postulado
  necessário [[9]](#ref9), mas o postulado de Bertrand é aqui uma dependência
  matemática externa, não um teorema Stainless neste desenvolvimento.

- **Ponte de contagem para período.** [§5.1](#51-exact-survivor-count) verifica
  que filtrar a janela completa expandida do estágio atual deixa exatamente
  $T(h-1)$ valores. [§6.3](#63-semantic-pipeline-agreement) estabelece
  separadamente a concordância semântica do prefixo de lacunas, enquanto
  [§6.4](#64-conditional-next-cycle-reconstruction) reconstrói o próximo estágio
  quando $\ell'_{T'}=h'+M'$ é fornecido. A derivação dessa equação do próximo
  período canônico a partir da contagem de mesma cabeça é um teorema aberto de
  composição distinto.

- **Construção direta de ciclo para ciclo.** A repetição preserva os valores
  representados; filtrar as visões base e repetida dá listas iguais de
  sobreviventes e lacunas; o primeiro sobrevivente é a próxima cabeça; e o
  prefixo semântico de lacunas mescladas concorda com a próxima especificação.
  O teorema aberto de composição é a igualdade entre a lista filtrada de
  lacunas entre sobreviventes do ciclo repetido e esse prefixo semântico de
  lacunas mescladas, seguida pelo empacotamento dessas lacunas em uma nova
  integral de ciclo.

- **Nenhum teorema de persistência de lacunas em janela curta.** [§5.2](#52-exact-lifted-copy-law-for-a-real-2-gap) prova que exatamente
  $h-2$ levantamentos de uma lacuna 2 linear real mantêm ambos os extremos ao
  longo de um bloco completo de levantamento. Isso não implica que um desses
  levantamentos esteja em um intervalo mais curto como $[h,h^2)$, nem ainda
  agrega a lacuna de volta cíclica em uma recorrência total do próximo estágio.
  Este artigo não faz nenhuma afirmação sobre infinitos primos gêmeos nem sobre
  a sobrevivência de lacunas 2 em toda janela local.

- **Nenhum teorema de eficiência.** O período cresce de $T$ para $T(h-1)$. O
  ciclo finito é analiticamente útil, mas materializá-lo não necessariamente
  supera uma peneira segmentada convencional. Nenhuma vantagem de complexidade
  de tempo ou espaço é reivindicada.

Essas qualificações fazem parte do resultado: elas separam o teorema verificado
de estágio finito das questões matemáticas adjacentes.

<a id="8-open-proof-work"></a>

## 8. Trabalho de Prova Aberto

A principal obrigação aberta de prova é conectar as lacunas entre sobreviventes
do ciclo repetido filtrado com o prefixo semântico de lacunas mescladas. Essa
igualdade é a ponte ausente entre a descrição local de deletar-e-mesclar e a
lista concreta de lacunas do próximo nível da peneira. Uma vez que essa ponte
seja verificada, a próxima `CycleIntegral` poderá ser construída diretamente a
partir do ciclo atual repetido e filtrado, em vez de ser relacionada por meio de
uma transição semântica separada.

Uma segunda obrigação aberta é derivar a próxima fronteira de período canônico a
partir da contagem exata de sobreviventes. O artigo já prova a lei de contagem
de período completo, mas a fronteira canônica exige transformar essa contagem no
prefixo finito preciso usado pelo próximo estágio. A dependência de limite
quadrático atualmente fornecida pelo postulado de Bertrand é outro alvo natural
de verificação: ou uma prova em Stainless do limite necessário, ou um substituto
formal claramente declarado, tornaria a dependência explícita dentro do projeto.

Teoremas locais de distribuição de lacunas permanecem separados dos resultados
de construção em período completo provados aqui. Os fatos de período completo
explicam como o estágio da peneira é representado e transformado; eles não
decidem por si mesmos quais lacunas aparecem em uma janela finita particular.

<a id="9-conclusion"></a>

## 9. Conclusão

A Sequência de Peneira é uma representação finita de um fluxo infinito de
valores aceitos. A formalização verifica os seguintes fatos centrais:

```math
\begin{aligned}
A_S(v)
&\Longrightarrow \exists i\ge0,\ \ell_i=v,
  &&\text{[Enumeração completa]} \\
\ell_{k+1}&\gt\ell_k,
  &&\text{[Crescimento estrito]} \\
\ell_{k+nT}&=\ell_k+nM,
  &&\text{[Deslocamento por bloco]}.
\end{aligned}
```

O ciclo finito de lacunas reconstrói o mesmo fluxo e permanece semanticamente
inalterado quando o ciclo é repetido:

```math
\begin{aligned}
I_G(k-1)&=\ell_k,
  &&\text{[Reconstrução do ciclo]} \\
I_{G^{\langle h\rangle}}(k)&=I_G(k),
  &&\text{[Invariância por repetição]}.
\end{aligned}
```

Instalar a cabeça atual como novo filtro tem uma contagem exata de período
completo, uma lei exata de cópias levantadas para cada lacuna 2 linear real e
uma atualização local de lacunas por copiar-ou-mesclar:

```math
\begin{aligned}
N_{\mathrm{survive}}&=T(h-1),
  &&\text{[Filtragem expandida exata]} \\
N_{\mathrm{destroyed\ lifts}}(\ell_k,\ell_{k+1})&=2,
  &&\text{[Ataques aos extremos de lacuna 2 real]} \\
N_{\mathrm{endpoint\text{-}surviving\ lifts}}(\ell_k,\ell_{k+1})&=h-2,
  &&\text{[Sobrevivência exata de cópias levantadas]} \\
g'_m&=g_k
  \quad\text{ou}\quad
  g'_m=\sum_{i=k}^{j-1}g_i,
  &&\text{[Copiar ou mesclar]}.
\end{aligned}
```

Sob as hipóteses explícitas de limite quadrático e fronteira de período, as
propriedades da próxima cabeça e da reconstrução do próximo estágio também são
verificadas:

```math
\begin{aligned}
p^+\lt h^2&\Longrightarrow \ell_1=p^+,
  &&\text{[Próxima cabeça]} \\
\text{mergedGaps}(S,S',1,T')
&=\text{gapList}(S',0,T'),
  &&\text{[Transição semântica]} \\
\ell'_{T'}=h'+M'
&\Longrightarrow I_{G'}(k-1)=\ell'_k.
  &&\text{[Próxima reconstrução condicional]}
\end{aligned}
```

A formalização, portanto, dá uma descrição precisa da peneira em estágio finito:
o padrão antigo de filtros se repete, a nova cabeça remove exatamente um
levantamento por resíduo antigo ao longo de um período expandido completo, os
dois ataques aos extremos de uma lacuna 2 linear real ocorrem em deslocamentos
de levantamento distintos, e a deleção muda lacunas apenas ao copiá-las ou
mesclá-las. O teorema não infere persistência de lacunas primas em janelas
curtas, uma recorrência populacional cíclica, nem eficiência algorítmica apenas
a partir dos fatos de período completo.

## Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Division and Modulo from Recursive
Normalization*. Disponível em: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009).

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists
Recursively Defined*. Disponível em: [https://rxiverse.org/abs/2609.0023](https://rxiverse.org/abs/2609.0023).

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*.
Disponível em: [https://doi.org/10.5281/zenodo.22865441](https://doi.org/10.5281/zenodo.22865441).

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from
First Principles*. Disponível em: [https://doi.org/10.5281/zenodo.22868423](https://doi.org/10.5281/zenodo.22868423).

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. e Wright, E. M. (1979). *An Introduction to the Theory of
Numbers* (5a ed.). Clarendon Press, Oxford. Ver Seção 5.4 para o Teorema
Chinês dos Restos e Seção 15.1 para a peneira de Eratóstenes.
[Registro bibliográfico](https://books.google.com/books?id=FlUj0Rk_rF4C).

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Pritchard, P. (1987). "Linear prime-number sieves: a family tree."
*Science of Computer Programming*, 9(1), 17-35.
[doi:10.1016/0167-6423(87)90024-4](https://doi.org/10.1016/0167-6423(87)90024-4).

<a name="ref7" id="ref7" href="#ref7">[7]</a>
EPFL-LARA. *Stainless documentation: Verification Conditions*.
[Official documentation](https://epfl-lara.github.io/stainless/verification.html).

<a name="ref8" id="ref8" href="#ref8">[8]</a>
Hamza, J., Voirol, N., e Kuncak, V. (2019). "System FR: Formalized
Foundations for the Stainless Verifier." *Proceedings of the ACM on Programming
Languages*, 3(OOPSLA), Article 166.
[doi:10.1145/3360592](https://doi.org/10.1145/3360592).

<a name="ref9" id="ref9" href="#ref9">[9]</a>
Ramanujan, S. (1919). "A proof of Bertrand's postulate." *Journal of the
Indian Mathematical Society*, 11, 181-182.
[Artigo original](https://ramanujan.sirinudi.org/Volumes/published/ram24.pdf).
