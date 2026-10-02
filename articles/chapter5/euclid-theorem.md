# Verificação Formal do Teorema de Euclides sobre a Infinitude dos Primos

**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)    
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**Licença:** [CC BY 4.0](../LICENSE)<br>
**Publicado:** [Zenodo:10.5281/zenodo.22929220](https://doi.org/10.5281/zenodo.22929220)

---

## Resumo

Apresentamos uma prova formalmente verificada do Teorema de Euclides — de que há infinitos números primos — usando o sistema de verificação Stainless. A prova usa a especialização familiar do primorial mais um da construção de Euclides para listas finitas: dada qualquer lista finita de primos, calculamos o produto deles mais um e mostramos que esse número tem um divisor primo que não está na lista original. A formalização se apoia em uma base de conhecimento prévio zero de aritmética modular e operações sobre listas, todas previamente verificadas a partir de primeiros princípios. O teorema descrito e os lemas de suporte são verificados por máquina usando um arcabouço mínimo e autocontido.

---

## 1. Introdução

O teorema de Euclides — provado nos *Elementos* de Euclides, Livro IX, Proposição 20
[[7]](#ref7) — afirma que há infinitos números primos. A apresentação
original de Euclides usa um múltiplo comum dos primos dados mais um.
Este artigo formaliza a especialização por produto (primorial) dessa
construção:

> Dada qualquer lista finita de primos $p_1, p_2, \dots, p_k$, seja $N = p_1 \cdot p_2 \cdot \dots \cdot p_k + 1$.
> Então $N$ ou é ele próprio primo, ou tem um divisor primo $d$ que não está entre $p_1, \dots, p_k$.
> Em ambos os casos, um novo primo é encontrado, provando que a lista não pode conter todos os primos.

Neste artigo, formalizamos e verificamos essa prova usando [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1), um arcabouço de verificação para programas Scala puros. Nossa abordagem segue a metodologia de conhecimento prévio zero estabelecida em artigos anteriores: aritmética modular [[2]](#ref2), listas [[3]](#ref3) e utilitários de primos são todos definidos desde o início e verificados independentemente.

Este artigo verifica:

- O primorial mais um é coprimo com todos os primos da lista — [§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes)
- Um novo primo é encontrado pela construção de Euclides — [§3.2](#32-stage-2-finding-a-new-prime)
- O novo primo não está na lista original — [§3.3](#33-stage-3-proving-the-new-prime-is-not-in-the-list)
- Teorema de Euclides: os primos são infinitos — [§3.4](#34-the-main-theorem)
- Lemas verificados de suporte sobre primos — [§4](#4-supporting-verified-lemmas)

<a id="2-preliminaries"></a>
## 2. Preliminares

Reutilizamos várias operações básicas e suas propriedades verificadas de artigos complementares:

- **Aritmética Modular** [[2]](#ref2): divisão, módulo, invariância do quociente, idempotência do módulo
- **Listas** [[3]](#ref3): tamanho, concatenação, soma, fatiamento, deslocamento da cauda
- **Utilitários de Primos:** cálculo de primorial, teste de primalidade e busca finita de divisores, especificados abaixo

<a id="21-key-definitions"></a>
### 2.1 Definições Principais

Seja $L = [p_1, p_2, \dots, p_k] \in \mathbb{N}^k$ uma lista não vazia de primos, com $p_i > 1$ para todo $i$.

Definimos o **primorial** de uma lista de primos como o produto de todos os primos na lista:

```math
\begin{aligned}
\text{primorial}(L) = \prod_{i=1}^{k} p_i
\end{aligned}
```

Um número $n$ é **primo** exatamente quando é maior que $1$ e nenhum inteiro
em $[2,n)$ o divide:

```math
\text{isPrime}(n) \;:\Longleftrightarrow\; n>1\ \land\
\forall d\in[2,n),\ \text{mod}(n,d)\ne0.
```

<a id="22-finite-prime-operations-and-their-specifications"></a>
### 2.2 Operações Finitas sobre Primos e Suas Especificações

O artigo precisa apenas de busca finita e das definições abaixo; ele não
assume uma enumeração externa de todos os primos. O primorial é estrutural:

```math
\begin{aligned}
\text{primorial}([]) &:= 1, \\
\text{primorial}(p::P) &:= p\cdot\text{primorial}(P).
\end{aligned}
```

Para $n>1$ e $2\leq s\leq n$, `findSmallestDivisor(n,s)` testa
$s,s+1,\ldots,n$ em ordem e retorna o primeiro divisor. Ela termina
porque o próprio $n$ divide $n$. Portanto, sua especificação é

```math
\begin{aligned}
d &= \text{findSmallestDivisor}(n,s) \\
&\implies s\leq d\leq n\ \land\ \text{mod}(n,d)=0 \\
&\qquad\land\ \forall e\in[s,d),\ \text{mod}(n,e)\ne0.
\end{aligned}
```

A varredura recursiva prova isso por indução em $n-s$: ou $s$ divide
$n$, ou a mesma afirmação é herdada da chamada que começa em $s+1$.
Assim, quando $s=2$, `d=n` é equivalente à definição de primo em
[§2.1](#21-key-definitions); se $d<n$, então $d$ é o menor divisor não trivial.
A pós-condição do intervalo de divisores é codificada em
[`Prime::findSmallestDivisor`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/Prime.scala).
Sua minimalidade e sua equivalência com um intervalo de divisores vazio são
verificadas por máquina por `Prime::assertFindSmallestDivisorMinimality` e
`Prime::assertFindSmallestDivisorEquivNoDivisorInRange` no mesmo código-fonte.

Para uma lista $P$ de inteiros positivos, `isCoprime(n,P)` significa que nenhum membro de
$P$ divide $n$; trata-se de uma recursão direta sobre a lista. Esse é o único
sentido de coprimalidade com lista usado abaixo.

<a id="3-the-proof-strategy"></a>
## 3. A Estratégia da Prova

O teorema de Euclides é formalizado como o seguinte lema:

```math
\begin{aligned}
\forall\ \text{primes} \in \text{List[Prime]},\ \text{primes} \neq \emptyset \implies
\exists\ p \notin \text{primes} : \text{isPrime}(p)
\end{aligned}
```

No código-fonte, isso é expresso por `PrimeProperties::euclidTheorem`; a
referência de verificação é dada em [§3.4](#34-the-main-theorem) e no Apêndice A.3.

- Etapa 1: $\text{primorial}(L)+1$ é coprimo com todo primo na lista ([§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes))
- Etapa 2: encontrar um divisor primo de $\text{primorial}(L)+1$ via `findSmallestDivisor` ([§3.2](#32-stage-2-finding-a-new-prime))
- Etapa 3: o novo primo não está na lista original ([§3.3](#33-stage-3-proving-the-new-prime-is-not-in-the-list))
- Teorema principal: combinar as etapas 1-3 no teorema de Euclides ([§3.4](#34-the-main-theorem))

A prova procede em três etapas:

1. **O primorial mais um não é divisível por nenhum primo da lista**: mostrar que $\text{primorial}(L) + 1 \bmod p_i = 1 \neq 0$ para todo $p_i \in L$.
2. **O menor divisor é um novo primo**: encontrar o menor divisor $d > 1$ de $\text{primorial}(L) + 1$. Provar que $d$ é primo e não está na lista original.
3. **Construir o resultado**: retornar ou $d$ (se $d < \text{primorial}(L) + 1$) ou o próprio $\text{primorial}(L) + 1$ (se ele for primo).

<a id="31-stage-1-primorial-plus-one-modulo-all-primes"></a>
### 3.1 Etapa 1: Primorial Mais Um Módulo Todos os Primos

A primeira etapa é capturada pelo lema `primorialPlusOneModAny`. Seja
$L = [p_1,\dots,p_k]$ a lista finita de primos conhecidos e
$P=\text{primorial}(L)$. Para cada $p_i \in L$, o produto $P$
contém $p_i$ como um fator, portanto $P$ é divisível por $p_i$. Adicionar um desloca
o resíduo de $0$ para $1$, e como todo primo é maior que $1$, esse
resíduo é não zero.

```math
\begin{aligned}
\text{primorial}(L)
  &= p_i \cdot \prod_{j\ne i} p_j
  &&\text{[By Definition]} \\
\text{mod}(\text{primorial}(L), p_i)
  &= 0
  &&\text{[Product Contains }p_i\text{]} \\
\text{mod}(\text{primorial}(L)+1, p_i)
  &= \text{mod}(1, p_i)
  &&\text{[Modulo Shift]} \\
  &= 1
  &&\text{[Since }1 < p_i\text{]} \\
  &\ne 0
  &&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

O código-fonte verificado prova isso por indução sobre a lista. Em cada passo, o
primo atual é separado do produto primorial, a divisibilidade do
produto restante é preservada pela multiplicação, e a hipótese de indução
continua sobre a cauda. O passo do laço é construído a partir de três propriedades
aritméticas verificadas.

**Resto de Dividendo Pequeno.** Um dividendo não negativo menor que o divisor já é
seu próprio resto. No passo de Euclides, isso dá tanto
$\text{mod}(0,p)=0$ quanto $\text{mod}(1,p)=1$ porque $p>1$.

```math
\begin{aligned}
0 \le a < b
&\Rightarrow \text{mod}(a,b)=a
&&\text{[Small Dividend]} \\
p>1
&\Rightarrow \text{mod}(0,p)=0
\land \text{mod}(1,p)=1
&&\text{[Substitution]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModSmallDividend::modSmallDividend
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModSmallDividend.scala).

**Resto Zero Preservado por Multiplicação.** Se um número é divisível por
$b$, multiplicá-lo por qualquer fator não negativo preserva a divisibilidade por $b$.
Este é o passo que transforma o fator explícito $p$ no primorial em
$\text{mod}(p\cdot k,p)=0$.

```math
\begin{aligned}
\text{mod}(a,b)=0
&\Rightarrow \text{mod}(a\cdot m,b)=0
&&\text{[Multiplication Preserves Zero Remainder]} \\
\text{mod}(p,p)=0
&\Rightarrow \text{mod}(p\cdot k,p)=0
&&\text{[Substitution]}
\end{aligned}
```

Esta propriedade é verificada em [
  AdditionAndMultiplication::ATimesBSameMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala).

**Adicionar Um Após um Múltiplo.** Uma vez que se sabe que a parte primorial é
divisível por $p$, adicionar um produz o mesmo resto que o próprio um.
Junto com a propriedade de dividendo pequeno, isso prova que o número de Euclides tem
resto não zero módulo todo primo original.

```math
\begin{aligned}
\text{mod}(m,b)=0
&\Rightarrow \text{mod}(m+c,b)=\text{mod}(c,b)
&&\text{[Modulo Shift]} \\
\text{mod}(p\cdot k,p)=0
&\Rightarrow \text{mod}(p\cdot k+1,p)=\text{mod}(1,p)=1
&&\text{[Substitution]} \\
&\Rightarrow \text{mod}(p\cdot k+1,p)\ne0
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModOperations::modZeroPlusC
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala).

Esta propriedade é verificada em [
  PrimeProperties::primorialPlusOneModAny
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). Um trecho curto do invólucro público está incluído no Apêndice A.1.

<a id="32-stage-2-finding-a-new-prime"></a>
### 3.2 Etapa 2: Encontrando um Novo Primo

Depois que sabemos que $\text{primorial}(L)+1$ não é divisível por nenhum primo em
$L$, seja

```math
\begin{aligned}
N &= \text{primorial}(L)+1, \\
d &= \text{findSmallestDivisor}(N,2).
\end{aligned}
```

Há dois casos. Se $d=N$, a busca de divisor não encontrou nenhum divisor próprio em
$[2,N)$, portanto $N$ é primo. Se $d < N$, então $d$ divide $N$ e nenhum inteiro menor
maior que $1$ divide $N$. Se $d$ fosse composto, ele teria um divisor não trivial
$e$ com $1 < e < d$; como $e$ divide $d$ e $d$ divide $N$, $e$ também
dividiria $N$, contradizendo a minimalidade de $d$. Logo $d$ é primo.

```math
\begin{aligned}
d=N
&\Rightarrow \forall e\in[2,N),\text{mod}(N,e)\ne0.         &&\text{[No Proper Divisor Found]} \\
&\Rightarrow \text{isPrime}(N)                              &&\text{[Prime Definition]} \\
&d < N \land \text{mod}(N,d)=0 \Rightarrow \text{isPrime}(d)  &&\text{[Minimal Divisor]} \\
\end{aligned}
```

A construção do novo primo é verificada em [
  PrimeProperties::newPrimeFromEuclid
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). Um trecho curto do invólucro público está incluído no Apêndice A.2.

<a id="33-stage-3-proving-the-new-prime-is-not-in-the-list"></a>
### 3.3 Etapa 3: Provando que o Novo Primo Não Está na Lista

A etapa final e mais sutil é provar que o primo recém-encontrado $d$ (ou
o próprio $N$) **não** está na lista original.

Seja $v$ o divisor escolhido na Etapa 2: ou $v=N$ quando $N$ é primo, ou
$v=d$ quando $d$ é o menor divisor próprio de $N$. Em ambos os casos,
$\text{mod}(N,v)=0$. Agora tome qualquer primo $p$ da lista original.
Como $N=\text{primorial}(L)+1$, o mesmo argumento da Etapa 1 dá
$\text{mod}(N,p)=1$. Se $p=v$, então $N$ teria dois restos incompatíveis
módulo o mesmo divisor positivo: $0$ e $1$. Portanto, nenhum elemento
de $L$ é igual a $v$.

```math
\begin{aligned}
N &= \text{primorial}(L) + 1
&&\text{[Euclid Construction]} \\
  &= p \cdot k + 1
&&\text{[Unfold Product at }p\text{]} \\
\text{mod}(N,p)
  &= \text{mod}(p\cdot k+1,p) \\
  &= \text{mod}(1,p)
&&\text{[Multiple of }p\text{ Drops Out]} \\
  &= 1
&&\text{[Since }p>1\text{]} \\
\text{mod}(N,v)
  &= 0
&&\text{[Chosen Divisor]} \\
p=v
  &\Rightarrow 1=0
&&\text{[Contradiction]} \\
\therefore\ p &\ne v
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esse argumento de não pertencimento é verificado pelo auxiliar privado
`euclidTailLoop`, que estabelece `valueNotMatchesAny(primes, v)` para o
divisor escolhido $v$ em [
  PrimeProperties
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

<a id="34-the-main-theorem"></a>
### 3.4 O Teorema Principal

O teorema principal combina o lema do primorial mais um, a primalidade do
menor divisor e o argumento de não pertencimento. Se $N$ é primo, então o próprio $N$ é
o novo primo. Caso contrário, o menor divisor $d$ de $N$ é primo e não pode
pertencer à lista original.

```math
\begin{aligned}
L &\ne [] \\
N &= \text{primorial}(L)+1 \\
d &= \text{findSmallestDivisor}(N,2) \\
d=N
&\Rightarrow \text{isPrime}(N)\land N\notin L
&&\text{[Stages 2 and 3]} \\
d < N
&\Rightarrow \text{isPrime}(d)\land d\notin L
&&\text{[Stages 2 and 3]} \\
\therefore\ \exists p:\text{isPrime}(p)\land p\notin L
&&\text{[Case Split]}\quad\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  PrimeProperties::euclidTheorem
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). O invólucro público do teorema é mostrado no Apêndice A.3.

<a id="4-supporting-verified-lemmas"></a>
## 4. Lemas Verificados de Suporte

O teorema acima é o principal resultado do artigo. Também registramos alguns lemas
intimamente relacionados que reutilizam as mesmas bases sobre primos e divisibilidade.
Eles são incluídos aqui como resultados de suporte, não como afirmações principais
adicionais.

- Consequência de prefixo finito: um prefixo finito completo dos primos tem um primo maior — [§4.1](#41-corollary-greater-than-a-complete-finite-prefix)
- Limites da busca de divisores: entradas compostas têm um menor divisor próprio abaixo de sua raiz quadrada — [§4.2](#42-smallest-divisor-bounds-for-composite-numbers)
- Critério de primalidade para prefixo finito: coprimalidade mais cobertura por fatores exclui todos os divisores próprios — [§4.3](#43-finite-prefix-primality-criterion)
- Lemas de produto de Bézout: um divisor primo de um produto é forçado a aparecer em um fator — [§4.4](#44-bézout-and-prime-product-lemmas)

<a id="41-corollary-greater-than-a-complete-finite-prefix"></a>
### 4.1 Corolário: Maior que um Prefixo Finito Completo

Um corolário direto da construção de Euclides é que um prefixo finito completo
dos primos nunca é fechado. Seja $P=[p_1,\dots,p_k]$ uma lista finita ordenada
que contém todo primo até seu maior elemento $h=p_k$. Seja $q$ o
primo produzido pela construção de Euclides a partir de $P$. Como [§3](#3-the-proof-strategy) prova
$q\notin P$, $q$ não pode estar em $h$ nem abaixo de $h$: todo primo menor ou igual a $h$ já está
contido no prefixo completo. Portanto $q > h$.

```math
\begin{aligned}
P &= [p_1,\dots,p_k],\quad h=p_k
&&\text{[Finite Prime Prefix]} \\
\forall r,\ \text{isPrime}(r)\land r\le h
&\Rightarrow r\in P
&&\text{[Prefix Complete Through }h\text{]} \\
\text{isPrime}(q)\land q\notin P
&&\text{[Euclid Construction]} \\
q\le h
&\Rightarrow q\in P
&&\text{[Prefix Completeness]} \\
q\le h
&\Rightarrow q\in P\land q\notin P
&&\text{[Contradiction]} \\
\therefore\ q&>h
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Essa é a forma de prefixo ordenado do teorema de Euclides: a partir de qualquer prefixo finito completo
dos primos, a construção produz um primo além desse prefixo.

Este corolário é verificado em [
  PrimeProperties::newPrimeNotInList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), [
  PrimeProperties::notContainsFromValueNotMatchesAny
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), and [
  PrimeProperties::euclidPrimeGreaterThanHead
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

<a id="42-smallest-divisor-bounds-for-composite-numbers"></a>
### 4.2 Limites do Menor Divisor para Números Compostos

O teste de primalidade usado na prova de Euclides depende de `findSmallestDivisor(n, 2)`,
que varre candidatos a partir de 2 até encontrar o menor divisor de $n$.
Dois lemas caracterizam por que essa varredura é correta e eficiente.

**Todo composto tem um divisor abaixo de n.** Se $n$ é composto e $d$ é seu menor
divisor não trivial, então $d < n$. Isso é imediato pela definição de
composto — existe um divisor próprio — mas deve ser provado em relação ao
algoritmo `findSmallestDivisor`, que varre para cima até que um divisor seja encontrado
ou que o próprio $n$ seja alcançado.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
\exists\, d = \text{findSmallestDivisor}(n, 2) &: 2 \leq d < n \;\land\; \text{Calc.mod}(n, d) = 0
\end{aligned}
```

**Prova.** Como $n$ é composto, ele tem um divisor próprio
$e\in[2,n)$. A especificação de minimalidade de [§2.2](#22-finite-prime-operations-and-their-specifications) dá
$2\leq d\leq e<n$ e $\text{mod}(n,d)=0$.

```math
\therefore\ 2\leq d\lt n\ \land\ \text{mod}(n,d)=0.
\quad \blacksquare\ \text{[Q.E.D.]}
```

**O menor divisor é no máximo sqrt(n).** Quando $n$ é composto com menor
divisor $d$, o fator $q = n / d$ satisfaz $q \ge d$. Então $d \cdot d \le d \cdot q = n$,
logo $d^2 \le n$. Isso significa que a varredura só precisa verificar divisores até $\sqrt{n}$
— qualquer divisor além disso teria um cofator abaixo de $d$, violando
a minimalidade.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
d = \text{findSmallestDivisor}(n, 2) &: d \cdot d \leq n.
\end{aligned}
```

**Prova.** Tome $q=n/d$. Como $d$ divide $n$, $dq=n$. Como $d<n$,
$q>1$; portanto $q\ge2$. Se $q<d$, então $q\in[2,d)$ é um divisor de $n$,
contradizendo a minimalidade de $d$.
Logo $d\leq q$, e

```math
d^2\leq dq=n.\quad\blacksquare\ \text{[Q.E.D.]}
```

**Divisor composto empacotado.** O invólucro `assertCompositeSmallestPrimeDivisor`
combina os resultados anteriores em uma forma reutilizável: todo
número composto tem um divisor primo não trivial, o divisor realmente divide
o número, e ele está no limite da raiz quadrada ou abaixo dele.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n)
&\Rightarrow \exists d: \\
&2 \le d < n
\;\land\; \text{isPrime}(d)
\;\land\; d^2 \le n
\;\land\; \text{Calc.mod}(n,d)=0
  &&\text{[Composite Smallest Prime Divisor]}
\end{aligned}
```

**Prova.** A partir da hipótese de composição, `assertCompositeHasDivisorStrictlyBelowN(n)`
dá $d < n$ com $\text{mod}(n, d) = 0$. Seja $q = n / d$, então $q \cdot d = n$.
Se $q < d$, então $q$ é um divisor de $n$ menor que $d$, contradizendo que $d$
é o menor divisor. Portanto $q \ge d$, e $d \cdot d \le d \cdot q = n$.

Essas propriedades são verificadas em [
  PrimeProperties::assertSmallestDivisorAtMostSqrt
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), [
  PrimeProperties::assertCompositeHasDivisorStrictlyBelowN
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), and [
  PrimeProperties::assertCompositeSmallestPrimeDivisor
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

<a id="43-finite-prefix-primality-criterion"></a>
### 4.3 Critério de Primalidade por Prefixo Finito

O próximo resultado de suporte é um critério local de primalidade. Se um número
candidato é coprimo com todos os primos em uma lista finita de filtros, e todo inteiro no
intervalo $[2, head)$ tem um fator primo entre esses filtros, então o
próprio candidato é primo.

Este não é o teorema da infinitude de Euclides; é um critério de primalidade por prefixo finito.
Ele transforma cobertura de todos os divisores possíveis menores em primalidade
do candidato.

```math
\begin{aligned}
head > 1
\;\land\; \text{isCoprime}(head,\overline P)
\;\land\;
\forall d\in[2,head),\ \neg \text{isCoprime}(d,\overline P)
&\Rightarrow \text{isPrime}(head).
\end{aligned}
```

A prova é por contradição sobre possíveis divisores. Se existisse um divisor $d$ de
$head$ em $[2, head)$, a hipótese de cobertura do intervalo forneceria um
fator primo da lista finita de filtros dividindo $d$. A divisibilidade então
se propagaria desse fator por $d$ até $head$, contradizendo que $head$
é coprimo com todo primo de filtro.

Esta propriedade é verificada em [
  PrimeProperties::assertHeadIsPrime
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). Seu principal auxiliar de intervalo é [
  PrimeProperties::assertNoDivisorInRangeFromHelper
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

<a id="44-bézout-and-prime-product-lemmas"></a>
### 4.4 Lemas de Bézout e Produto por Primo

Vários argumentos sobre produtos filtrados por primos usam uma forma de produto da
primalidade: para um primo $p$, a divisibilidade de um produto não negativo por $p$ pode
ser empurrada para um fator, e se nenhum fator não negativo é divisível por
$p$, então o produto não é divisível por $p$. A prova verificada passa pela
identidade de Bézout.

Primeiro, se $0 < h < p$, $p$ é primo, e $h$ não é divisível por $p$, então
$h$ e $p$ têm máximo divisor comum $1$, e o algoritmo euclidiano estendido
expõe uma combinação linear:

```math
\begin{aligned}
\text{isPrime}(p)
\land 0 < h < p
\land \text{mod}(h,p)\ne0
&\Rightarrow
\exists x,y,\ h x + p y = 1.
\end{aligned}
```

Para completude, o algoritmo euclidiano estendido subtrativo substitui repetidamente
a maior entrada positiva por sua diferença com a menor. Divisores comuns
são preservados e a soma positiva diminui, então ele alcança valores iguais.
Reverter qualquer passo de subtração preserva uma testemunha de combinação linear:

```math
\begin{aligned}
(a-b)x+by=g &\implies ax+b(y-x)=g, \\
ax+(b-a)y=g &\implies a(x-y)+by=g.
\end{aligned}
```

Todo divisor comum de $h$ e do primo $p$ é ou $1$ ou $p$; ele não pode
ser $p$ porque $0<h<p$. Portanto, o mdc terminal é $1$, o que dá a
identidade de Bézout exibida. [Q.E.D.]

Multiplicar essa identidade por $k$ dá $k h x + k p y = k$. Se $p$ divide
$k h$, então $p$ divide ambos os termos à esquerda e, portanto, divide $k$.

```math
\begin{aligned}
\text{isPrime}(p)
\land k\ge0
\land h\ge0
\land \text{mod}(h,p)\ne0
\land \text{mod}(kh,p)=0
&\Rightarrow \text{mod}(k,p)=0.
\end{aligned}
```

A forma contrapositiva usada por argumentos de produto e densidade é:

```math
\begin{aligned}
\text{isPrime}(p)
\land k\ge0
\land h\ge0
\land \text{mod}(k,p)\ne0
\land \text{mod}(h,p)\ne0
&\Rightarrow \text{mod}(kh,p)\ne0.
\end{aligned}
```

Os corpos completos das provas são verificados em [
  BezoutUtils::assertCoprimeLinearCombinationOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala), [
  BezoutUtils::assertPrimeDivKhImpliesDivK
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala), and [
  BezoutUtils::assertPrimeProductNotDivisible
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala).

## 5. Estado da Verificação

As propriedades descritas neste artigo são verificadas pelo Stainless por meio das
funções de prova vinculadas ao código-fonte citadas nas seções relevantes e no Apêndice A.
A contagem de condições de verificação de todo o repositório é omitida intencionalmente
porque ela muda à medida que módulos verificados não relacionados são adicionados; a afirmação estável é
que a prova do teorema de Euclides e seus lemas de suporte sobre primos são
verificados por máquina no código-fonte atual.

## 6. Trabalhos Relacionados

Os fundamentos de aritmética modular e listas usados aqui são citados em
[§2](#2-preliminaries). A construção clássica de Euclides fornece o
argumento matemático; este artigo contribui com sua formalização recursiva em Scala/Stainless
junto com a busca finita de divisores especificada explicitamente.
Para comparação, a Mathlib também formaliza a infinitude dos primos como
`Nat.exists_infinite_primes` [[8]](#ref8). Esse teorema tem um
ambiente de biblioteca e uma forma de enunciado diferentes; é trabalho relacionado, não uma dependência
deste desenvolvimento.

## 7. Conclusão

Este artigo formaliza o teorema de Euclides a partir da mesma base de primeiros princípios
usada ao longo dos capítulos anteriores. A prova segue a construção clássica do
primorial mais um: a partir de uma lista finita de primos, ela constrói
um número que é congruente a um módulo todo primo da lista, e então
usa a existência de um menor divisor para extrair um fator primo fora dessa
lista. A contradição é matemática antes de ser computacional: nenhum membro
da lista original pode dividir o número construído, enquanto o número construído
ainda deve ter um divisor primo.

O desenvolvimento em Stainless verifica cada passo do qual o artigo depende:
fatos sobre restos pequenos, preservação de resto zero sob multiplicação,
divisibilidade de membros de produtos, primalidade do menor divisor e o teorema final
de não pertencimento. O resultado é uma prova formal, respaldada por código-fonte, da
infinitude dos primos, com os corolários de prefixo finito separados
do eixo do teorema em vez de incorporados à afirmação principal.

O eixo do teorema pode ser lido de forma compacta como a seguinte cadeia verificada. Seja
$P=\text{primorial}(L)$ e $N=P+1$:

```math
\begin{aligned}
\forall p\in L,\quad \text{mod}(N,p)&=1\ne0
&&\text{[Stage 1]} \\
d=\text{findSmallestDivisor}(N,2),\quad d=N
&\Rightarrow \text{isPrime}(N) \\
d\lt N
&\Rightarrow \text{isPrime}(d)
&&\text{[Stage 2]} \\
v\mid N\ \land\ p\in L
&\Rightarrow p\ne v
&&\text{[Stage 3].}
\end{aligned}
```

Assim, ou $N$, ou seu menor divisor não trivial $d$, é um primo fora de
$L$:

```math
L\ne[]\ \Rightarrow\ \exists p:\text{isPrime}(p)\land p\notin L.
\quad\blacksquare\ \text{[Q.E.D.]}
```

## 8. Trabalhos Futuros

A continuação mais natural é o Teorema Fundamental da Aritmética, pois
o teorema de Euclides já estabelece o lado de existência da decomposição
em primos. Uma prova verificada de unicidade exigiria uma biblioteca mais forte de
lemas de divisibilidade e coprimalidade, mas estenderia o resultado presente de
modo direto e estruturalmente compatível.

Trabalhos futuros poderiam então passar da existência para a distribuição. O
teorema de Dirichlet exigiria progressões aritméticas e raciocínio modular substancialmente
mais rico, enquanto o Teorema dos Números Primos exigiria análise assintótica muito
além da aritmética finita desenvolvida aqui. Essas direções estão intencionalmente
fora do escopo deste artigo, mas esta prova fornece um ponto de partida verificado
para elas.

## Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Division and Modulo from Recursive Normalization*. Disponível em: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Disponível em: [https://rxiverse.org/abs/2609.0023](https://rxiverse.org/abs/2609.0023)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Discrete Integration Properties from First Principles*. Disponível em: [https://doi.org/10.5281/zenodo.22746792](https://doi.org/10.5281/zenodo.22746792)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*. Disponível em: [https://doi.org/10.5281/zenodo.22865441](https://doi.org/10.5281/zenodo.22865441)

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Disponível em: [https://doi.org/10.5281/zenodo.22868423](https://doi.org/10.5281/zenodo.22868423)

<a name="ref7" id="ref7" href="#ref7">[7]</a>
Euclides. *Elementos*, Livro IX, Proposição 20. Tradução e notas de David E.
Joyce. Disponível em: [https://aleph0.clarku.edu/~djoyce/java/elements/bookIX/propIX20.html](https://aleph0.clarku.edu/~djoyce/java/elements/bookIX/propIX20.html)

<a name="ref8" id="ref8" href="#ref8">[8]</a>
The Mathlib Community. *Mathlib.Data.Nat.Prime.Infinite*: `Nat.exists_infinite_primes`.
Documentação da Mathlib. Disponível em: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Infinite.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Infinite.html)

---

## Apêndice A: Referências ao Código-Fonte de Verificação

### A.1 `primorialPlusOneModAny`

**Fonte**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Trecho curto do código-fonte para a Etapa 1 (Seção 3.1):

```scala
def primorialPlusOneModAny(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)
  decreases(primes.size)
  primorialPlusOneTailLoop(List.empty, primes)
}.holds
```

Este lema estabelece que $\text{primorial}(\text{primes}) + 1$ não é divisível por nenhum primo da lista, por meio do auxiliar recursivo `primorialPlusOneTailLoop` e dos lemas de aritmética modular citados em [§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes).

### A.2 `newPrimeFromEuclid`

**Fonte**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Trecho curto do código-fonte para a Etapa 2 (Seção 3.2):

```scala
def newPrimeFromEuclid(primes: List[Prime]): Prime = {
  require(primes.nonEmpty)
  require(primorialPlusOneModAny(primes))

  PrimeUtils.primorialPositive(primes)
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)

  if (d == n) {
    findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
    Prime(n)
  } else {
    assertSmallestDivisorIsPrime(n, d)
    findSmallestDivisorResultModZero(n, d)
    Prime(d)
  }
}
```

Esta função constrói um novo valor `Prime` encontrando o menor divisor de $n = \text{primorial}(\text{primes}) + 1$. Se $d = n$, então o próprio $n$ é primo; caso contrário, $d$ é um divisor primo. Em ambos os casos, o resultado é um primo que não está na lista original.

### A.3 `euclidTheorem`

**Fonte**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Trecho curto do código-fonte para o teorema principal (Seção 3.4):

```scala
def euclidTheorem(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)

  primorialPlusOneModAny(primes)
  PrimeUtils.primorialPositive(primes)
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)

  if (d == n) {
    findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
    assert(euclidTailLoop(primes, n, n, BigInt(1)))
    valueNotMatchesAny(primes, n)
  } else {
    assertSmallestDivisorIsPrime(n, d)
    findSmallestDivisorResultModZero(n, d)
    assert(euclidTailLoop(primes, d, n, BigInt(1)))
    valueNotMatchesAny(primes, d)
  }
}.holds
```

Esta prova no código-fonte é a forma verificada por máquina do teorema principal: toda
lista finita não vazia de primos admite um primo fora da lista.

## Apêndice B: Saída do Log de Verificação do Stainless

A execução mais recente de `just verify` verifica as propriedades descritas sem erros.
A saída completa do log está disponível em [logs/verify-ch-5-v1-chapter5-_.log](https://github.com/thiagomata/prime-numbers/blob/euclid-theorem-article-v1.0.0/logs/verify-ch-5-v1-chapter5-_.log).
