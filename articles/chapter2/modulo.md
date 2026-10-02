# Divisão e Módulo por Normalização Recursiva

**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)    
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**Licença:** [CC BY 4.0](../LICENSE)<br>
**Publicado:** [ai.viXra:2609.0009](http://ai.viXra.org/abs/2609.0009)<br>
**DOI:** [10.5281/zenodo.22955131](https://doi.org/10.5281/zenodo.22955131)

## Resumo

<div align="justify">
<p style="text-align: justify">

Definimos divisão inteira e módulo normalizando recursivamente estados de
quociente-resto e verificamos a construção em Scala Stainless. Provamos a
unicidade da solução normalizada, a compatibilidade com o módulo nativo para
dividendos não negativos e divisores positivos, a invariância sob deslocamentos
por múltiplos do divisor, junto com leis de adição, subtração e idempotência do
módulo. Também verificamos a transição quociente-resto por passo unitário e que
todo bloco de $p$ inteiros não negativos consecutivos, para $p > 1$, contém
exatamente um resto zero módulo $p$. Em conjunto, esses resultados mostram que a
normalização recursiva é canônica nos domínios declarados e recupera as leis
algébricas e periódicas verificadas da divisão e do módulo.

</p>
</div>

## 1. Introdução

As operações de divisão inteira e módulo são ferramentas centrais em matemática
discreta, teoria dos números e algoritmos. Embora suas propriedades sejam bem
conhecidas, a formalização e a verificação rigorosas, em particular por meio de
definições recursivas, oferecem uma alternativa interessante ao modelo axiomático
tradicional.

Este artigo segue a rota recursiva. Em vez de assumir divisão e módulo nativos,
ele define um estado $DivMod(a,b,q,r)$ em que $a = bq + r$, e então prova que
normalizar o par $(q,r)$ preserva o dividendo representado e alcança o intervalo
canônico do resto. As operações familiares $\text{div}$ e $\text{mod}$ são então
projeções desse estado normalizado.

As afirmações matemáticas abaixo são sustentadas por código-fonte Scala
verificado com [Stainless](https://epfl-lara.github.io/stainless/intro.html). O
artigo mantém a discussão das provas centrada nas propriedades; os links de
código apontam para o código de verificação mantido.

Este artigo estabelece:

- Identidades fundamentais: caso trivial, autoidentidade, divisão por um e
  concordância com o operador de módulo nativo —
  [§6.1–6.4](#61-trivial-case)
- Leis de deslocamento linear sob adição do divisor em um passo e em múltiplos
  passos —
  [§6.5–6.6](#65-quotient-invariance-under-linear-shift)
- Unicidade e idempotência do resto normalizado —
  [§6.7–6.8](#67-unique-remainder)
- Distributividade de módulo e divisão sobre adição e subtração —
  [§6.9–6.10](#69-distributivity-over-addition)
- Invariância por deslocamento em base divisível e pares simétricos de restos —
  [§6.11–6.12](#611-modular-shift-invariance-under-divisible-base)
- A lei de incremento por passo unitário e a densidade de zeros sobre inteiros
  consecutivos —
  [§6.13–6.14](#613-unit-step-modulo-division-increment-law)

## 2. Limitações

A implementação apresentada neste artigo limita-se às operações de divisão e
módulo para inteiros. Seu objetivo é disponibilizar um conjunto de lemas e
provas que possam ser verificados e usados como base para provar outras
propriedades relacionadas às operações de divisão e módulo. Portanto, a
implementação é otimizada para correção, não para desempenho.

O uso de BigInt na implementação enfoca inteiros não limitados, sem a necessidade
de se preocupar com overflow ou underflow. Ainda assim, eles continuam
limitados pela memória disponível no sistema. De modo semelhante, alguns lemas e
provas usam a definição recursiva das operações de divisão e módulo, o que pode
causar estouro de pilha para números grandes. Esses pontos não invalidam as
propriedades matemáticas provadas neste artigo, que são o foco principal.

<a id="3-traditional-definition"></a>

## 3. Definição Tradicional

Dados inteiros $\text{dividend}$ e $\text{divisor}$ com
$\text{divisor} \neq 0$, o algoritmo da divisão determina inteiros
$\text{quotient}$ e $\text{remainder}$ tais que:

```math
\begin{aligned}
\forall \text{dividend},\text{divisor} \in \mathbb{Z},\;
\text{divisor} \neq 0,\;
\exists!\, \text{quotient},\text{remainder} &: \\
\text{dividend} &= \text{divisor} \cdot \text{quotient} + \text{remainder} \\
0 &\le \text{remainder} < |\text{divisor}| \\
\text{dividend} \text{ div } \text{divisor} &:= \text{quotient} \\
\text{dividend} \text{ mod } \text{divisor} &:= \text{remainder}
\end{aligned}
```

As duas primeiras linhas enunciam a relação de divisão e o intervalo canônico do
resto. As duas últimas introduzem a notação das operações: a divisão retorna o
quociente, e o módulo retorna o resto.

## 4. Definição Recursiva

Introduzimos uma definição recursiva de divisão e módulo porque a prova pode ser
construída a partir de um invariante: deslocar uma unidade de $b$ entre
quociente e resto preserva o dividendo representado. Na
[Seção 5](#5-divmod-solution-invariance-under-linear-shift), esse invariante
conecta a forma normal recursiva de volta à equação tradicional da divisão da
[Seção 3](#3-traditional-definition).

Daqui em diante, $a$ é o dividendo, $b$ é o divisor, $q$ é o quociente
candidato, e $r$ é o resto candidato. Os nomes mais curtos mantêm as equações
recursivas legíveis, preservando os mesmos papéis da definição tradicional.
Reservamos $\text{mod}$ para a própria operação de módulo.

Definimos $DivMod(a,b,q,r)$ de modo que:

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z} : b \neq 0,\; a = bq + r
\end{aligned}
```

Os estados $DivMod$ resolvidos são aqueles em que o resto $r$ satisfaz:

```math
\begin{cases}
0 \leq r < b & \text{if } b > 0, \\
0 \leq r < -b & \text{if } b < 0.
\end{cases}
```

```math
\begin{aligned}
\text{DivMod.solve}(a,b,q,r) &:=
\begin{cases}
\text{DivMod}(a,b,q,r) & \text{if } 0 \leq r < |b|, \\
\text{DivMod.solve}(a,b,q+\text{sign}(b),r-|b|) & \text{if } r \geq |b|, \\
\text{DivMod.solve}(a,b,q-\text{sign}(b),r+|b|) & \text{if } r < 0. \\
\end{cases} \\
\end{aligned}
```

A definição recursiva está implementada em [DivMod.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/DivMod.scala).


<a id="5-divmod-solution-invariance-under-linear-shift"></a>

## 5. Invariância da Solução DivMod sob Deslocamento Linear

Mover uma cópia do divisor entre quociente e resto preserva o dividendo
representado; portanto, a normalização alcança o mesmo estado final.

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z},\; b \neq 0,\; a &= bq + r \\
a &= b(q+1) + (r-b) \\
a &= b(q-1) + (r+b) \\
\text{DivMod}(a,b,q+1,r-b).\text{solve} &= \text{DivMod}(a,b,q,r).\text{solve} \\
\text{DivMod}(a,b,q-1,r+b).\text{solve} &= \text{DivMod}(a,b,q,r).\text{solve}
\end{aligned}
```

Esse invariante é verificado para o [deslocamento positivo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#assertDivModWithMoreDivAndLessModSameSolution) e o [deslocamento negativo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#assertDivModWithLessDivAndMoreModSameSolution).


### 5.1 Criando as Operações de Divisão e Módulo

Usando o valor `DivMod` normalizado, [Calc.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/Calc.scala) define $\text{div}$ e $\text{mod}$ como as projeções de quociente e resto
do estado resolvido. Partindo de $DivMod(a,b,0,a)$, seja:

```math
\begin{aligned}
S &:= \text{DivMod}(a,b,0,a).\text{solve} \\
q &:= S.\text{div} \\
r &:= S.\text{mod} \\
\text{div}(a,b) &:= q \\
\text{mod}(a,b) &:= r
\end{aligned}
```

Assim, $\text{div}(a,b)$ nomeia o quociente normalizado, enquanto
$\text{mod}(a,b)$ nomeia o resto normalizado. No código-fonte, esses são os
campos `div` e `mod` do `DivMod` resolvido; na notação do artigo, $q$ e $r$
mantêm os papéis de quociente e resto separados dos nomes das operações.

O artigo usa tanto notação funcional quanto infixa para as mesmas operações:
$\text{div}(x,y)$ e $x \text{ div } y$ são equivalentes, assim como
$\text{mod}(x,y)$ e $x \text{ mod } y$. A notação funcional é útil quando a
operação está aninhada em outra expressão; a notação infixa mantém identidades
algébricas simples mais próximas da apresentação tradicional.

## 6. Algumas Propriedades Importantes de Módulo e Divisão

Este capítulo desenvolve as identidades concretas que seguem das definições e
do invariante de deslocamento linear da
[Seção 5](#5-divmod-solution-invariance-under-linear-shift). Ele estabelece:

- Os casos-base em que a normalização é imediata: um dividendo pequeno,
  autodivisão, divisão por um e concordância com o operador de módulo nativo
  ([§6.1](#61-trivial-case)–[§6.4](#64-compatibility-with-native-modulo))
- Como um deslocamento único ou repetido do dividendo pelo divisor move o
  quociente sem perturbar o resto ([§6.5](#65-quotient-invariance-under-linear-shift)–[§6.6](#66-quotient-invariance-under-linear-shift-by-multiplier))
- A unicidade do resto normalizado e sua idempotência sob redução repetida
  ([§6.7](#67-unique-remainder)–[§6.8](#68-modulo-idempotence))
- Distributividade de módulo e divisão sobre adição e subtração
  ([§6.9](#69-distributivity-over-addition)–[§6.10](#610-distribution-over-subtraction))
- Invariância por deslocamento quando o dividendo já é divisível pela base, e
  a simetria dos pares de restos ao redor dessa base ([§6.11](#611-modular-shift-invariance-under-divisible-base)–[§6.12](#612-symmetrical-modulo-pairs))
- A lei de incremento por passo unitário e a densidade de restos zero ao longo
  de inteiros consecutivos ([§6.13](#613-unit-step-modulo-division-increment-law)–[§6.14](#614-consecutive-integers-zero-density))

<a id="61-trivial-case"></a>

### 6.1 Caso Trivial

Se o dividendo é menor que um divisor positivo, o estado candidato
$DivMod(a,b,0,a)$ já é final. Nenhuma subtração de $b$ é necessária, portanto o
quociente é zero e o resto é o dividendo original.

```math
\begin{aligned}
& \forall \text{ } a, b \in \mathbb{N} : b \neq 0 \\
& a < b \implies a \text{ mod } b & = a \\
& a < b \implies a \text{ div } b & = 0 \\
\end{aligned}
```

Esta propriedade é verificada em [
  ModSmallDividend
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModSmallDividend.scala).

### 6.2 Identidade

O módulo de todo número por ele mesmo é zero, e a divisão de todo número por ele
mesmo é um.

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} : n & \neq 0 \\
n \text{ mod } n & = 0 \\
n \text{ div } n & = 1 \\
\end{aligned}
```

O estado candidato normaliza em um deslocamento para o estado final com
quociente $1$ e resto $0$:

```math
\begin{aligned}
n &= n\cdot0+n = n\cdot1+0 \\
0 &\leq 0 < |n| \\
\text{DivMod}(n,n,0,n).\text{solve} &= \text{DivMod}(n,n,1,0).
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModIdentity::modIdentity
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdentity.scala). Uma prova mais longa
no código-fonte, mostrando o caminho de normalização, está disponível em [
  ModIdentity::longProof
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdentity.scala#longProof).

### 6.3 Módulo e Divisão por Um

Módulo por um sempre retorna zero, e divisão por um sempre retorna o dividendo.

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} & : \\
n \text{ mod } 1 & = 0 \\
n \text{ div } 1 & = n \\
\end{aligned}
```

Ambas as identidades seguem diretamente da decomposição já canônica
$n=1\cdot n+0$; nenhuma indução nem resultado posterior de passo unitário é
necessário.

```math
\begin{aligned}
n &= 1\cdot n+0,\qquad 0\leq0<1 \\
\text{mod}(n,1) &= 0,\qquad \text{div}(n,1)=n.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Essas propriedades são verificadas em [
  ModOne::modOneIsZero
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOne.scala) and [
  ModOne::divOneIsN
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOne.scala).

<a id="64-compatibility-with-native-modulo"></a>

### 6.4 Compatibilidade com o Módulo Nativo

Para dividendos não negativos e divisores positivos, o módulo normalizado
recursivamente concorda com o operador nativo `%` de BigInt.

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : a \geq 0,\; b > 0 \\
a \text{ mod } b & = a \mathbin{\%} b \\
\end{aligned}
```

Este não é um fato matemático novo, mas um lema de ponte: ele confirma que o
operador nativo `%` e o $\text{mod}$ definido recursivamente concordam em seu
domínio comum de dividendos não negativos e divisores positivos, de modo que
resultados derivados de um coincidem com resultados derivados do outro.

Esta propriedade é verificada em [
  ModNativeCompatibility::percentEqualsCalcMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModNativeCompatibility.scala#percentEqualsCalcMod).

<a id="65-quotient-invariance-under-linear-shift"></a>

### 6.5 Invariância do Quociente sob Deslocamento Linear

Adicionar ou subtrair o divisor do dividendo altera o quociente em uma unidade,
mas deixa o resto inalterado.

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + b, b) & = \text{mod}(a, b) \\
\text{div}(a + b, b) & = \text{div}(a, b) + 1 \\
\text{mod}(a - b, b) & = \text{mod}(a, b) \\
\text{div}(a - b, b) & = \text{div}(a, b) - 1 \\
\end{aligned}
```

Sejam $q=\text{div}(a,b)$ e $r=\text{mod}(a,b)$. O estado normalizado satisfaz
$a=bq+r$, com $r$ já no intervalo canônico do resto. Deslocar o dividendo por um
divisor produz dois estados igualmente canônicos:

```math
\begin{aligned}
a+b &= bq+r+b = b(q+1)+r \\
a-b &= bq+r-b = b(q-1)+r \\
\text{DivMod}(a+b,b,q+1,r).\text{solve} &= \text{DivMod}(a+b,b,q+1,r) \\
\text{DivMod}(a-b,b,q-1,r).\text{solve} &= \text{DivMod}(a-b,b,q-1,r).
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada para o [caso positivo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#APlusBSameModPlusDiv) e o [caso negativo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#ALessBSameModDecreaseDiv).

<a id="66-quotient-invariance-under-linear-shift-by-multiplier"></a>

### 6.6 Invariância do Quociente sob Deslocamento Linear por Multiplicador

Adicionar um múltiplo do divisor altera o quociente por esse multiplicador, mas
deixa o resto inalterado.

Como consequência direta das leis de deslocamento em um passo, também podemos
provar que:

```math
\begin{aligned}
\forall a,b,q,r,m \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + m \cdot b, b) & = \text{mod}(a, b) \\
\text{div}(a + m \cdot b, b) & = \text{div}(a, b) + m \\
\text{mod}(a - m \cdot b, b) & = \text{mod}(a, b) \\
\text{div}(a - m \cdot b, b) & = \text{div}(a, b) - m \\
\end{aligned}
```

Para $m\geq0$, a indução aplica a lei positiva de um passo a $a+m b$: o resto
permanece inalterado a cada passo e o quociente ganha uma unidade. Assim, o
resultado vale em $m=0$ e é preservado de $m$ para $m+1$. As identidades de
subtração seguem pela mesma indução usando a lei negativa de um passo. Se
$m<0$, escreva $m=-t$ com $t>0$ e troque as identidades de adição e subtração
recém-obtidas.

```math
\begin{aligned}
\text{mod}(a+(m+1)b,b) &= \text{mod}((a+mb)+b,b) = \text{mod}(a,b) \\
\text{div}(a+(m+1)b,b) &= \text{div}(a+mb,b)+1 = \text{div}(a,b)+m+1.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada para o [caso positivo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#APlusMultipleTimesBSameMod) e o [caso negativo](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#ALessMultipleTimesBSameMod).

<a id="67-unique-remainder"></a>

### 6.7 Resto Único

Existe apenas um único valor de resto para cada par $a,b$ com $b > 0$.

```math
\begin{aligned}
  \forall \text{ } a, b & \in \mathbb{N} : b > 0 \\
  \quad \exists ! \, r \in \mathbb{N} &: 0 \leq r < b \;\land\; a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r
\end{aligned}
```

em outras palavras, duas instâncias de $DivMod$ com o mesmo dividendo $a$ e o
mesmo divisor $b$ terão a mesma solução.

```math
\begin{aligned}
\forall a,b,q_x,r_x,q_y,r_y & \in \mathbb{N}, \\
\text{where } b & \neq 0 \text{, } \\
a & = bq_x + r_x \text{ and } \\
a & = bq_y + r_y \text{ then } \\
DivMod(a,b,q_x,r_x).solve & = DivMod(a,b,q_y,r_y).solve \\
\end{aligned}
```

Para todo par $a,b$, com quaisquer quocientes e restos candidatos $(q_x,r_x)$ e
$(q_y,r_y)$ representando o mesmo dividendo, a normalização alcança a mesma
solução.
Esta propriedade é verificada em [
  ModIdempotence::modUnique
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modUnique).

<a id="68-modulo-idempotence"></a>

### 6.8 Idempotência do Módulo

Tomar o módulo de um número duas vezes produz o mesmo resultado que tomá-lo uma
única vez.

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
\end{aligned}
```

Esta propriedade é verificada em [
  ModIdempotence::modIdempotence
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modIdempotence).

<a id="69-distributivity-over-addition"></a>

### 6.9 Distributividade sobre Adição

A operação de módulo distribui sobre a adição, isto é, o resto de uma soma é
igual ao resto da soma dos restos. Isso permite decompor operações de módulo
complexas em componentes mais simples.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a +  c) \text{ mod } b & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
\end{aligned}
```

Sejam $q_a=\text{div}(a,b)$, $r_a=\text{mod}(a,b)$,
$q_c=\text{div}(c,b)$ e $r_c=\text{mod}(c,b)$. Assim, $a=bq_a+r_a$ e
$c=bq_c+r_c$. Normalizar a soma dos dois restos dá $r_a+r_c=bs+t$, em que
$s=\text{div}(r_a+r_c,b)$ e $t=\text{mod}(r_a+r_c,b)$. A substituição fornece o
quociente e o resto de $a+c$:

```math
\begin{aligned}
a+c &= b(q_a+q_c)+(r_a+r_c) \\
    &= b(q_a+q_c+s)+t \\
t &= r_a+r_c-b\cdot\text{div}(r_a+r_c,b).
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModOperations::modAdd
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modAdd). A terceira identidade, isolando o múltiplo de $b$ subtraído,
é provada diretamente em [ModIdempotence.scala#modModPlus](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modModPlus).

<a id="610-distribution-over-subtraction"></a>

### 6.10 Distribuição sobre Subtração

De modo semelhante à adição, a operação de módulo distribui sobre a subtração. O
resto de uma diferença é igual ao resto da diferença dos restos, com tratamento
adequado para valores negativos.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ mod } b & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
\end{aligned}
```

Sejam $q_a=\text{div}(a,b)$, $r_a=\text{mod}(a,b)$,
$q_c=\text{div}(c,b)$ e $r_c=\text{mod}(c,b)$. Assim, $a=bq_a+r_a$ e
$c=bq_c+r_c$. Normalize a diferença $r_a-r_c=bs+t$. Então a decomposição
canônica de $a-c$ é obtida sem qualquer hipótese de que $r_a-r_c$ seja não
negativo:

```math
\begin{aligned}
a-c &= b(q_a-q_c)+(r_a-r_c) \\
    &= b(q_a-q_c+s)+t \\
t &= r_a-r_c-b\cdot\text{div}(r_a-r_c,b).
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModOperations::modLess
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modLess). A terceira identidade, isolando o múltiplo de $b$ subtraído,
é provada diretamente em [ModIdempotence.scala#modModMinus](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modModMinus).

<a id="611-modular-shift-invariance-under-divisible-base"></a>

### 6.11 Invariância de Deslocamento Modular sob Base Divisível

Quando um número é múltiplo do divisor (o módulo é zero), adicionar qualquer
valor não altera o módulo desse valor. Esta propriedade simplifica cálculos
quando um operando já é divisível pela base. Ela vale para qualquer inteiro
$c$, incluindo valores negativos.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a + c ) \text{ mod } b = c \text{ mod } b \\
\end{aligned}
```

A lei de adição de [§6.9](#69-distributivity-over-addition) reduz o lado
esquerdo ao módulo dos dois restos. A hipótese remove o primeiro, e a
idempotência do módulo remove a repetição restante:

```math
\begin{aligned}
\text{mod}(a+c,b) &= \text{mod}(\text{mod}(a,b)+\text{mod}(c,b),b) \\
&= \text{mod}(\text{mod}(c,b),b) \\
&= \text{mod}(c,b). \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModOperations::modZeroPlusC
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modZeroPlusC).

Substituir $-c$ por $c$ fornece diretamente o corolário de subtração, pois $c$
é irrestrito:

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a - c ) \text{ mod } b = ( -c ) \text{ mod } b \\
\end{aligned}
```

Este corolário é verificado pelo mesmo lema, [
  ModOperations::modZeroPlusC
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modZeroPlusC), chamado com $-c$ no lugar de $c$.

<a id="612-symmetrical-modulo-pairs"></a>

### 6.12 Pares Simétricos de Módulo

O módulo de um valor e o módulo de seu complemento em relação à base somam a
própria base.

```math
\begin{aligned}
b &> 0,\quad 0 < k < b \\
k \text{ mod } b + (b - k) \text{ mod } b & = b
\end{aligned}
```

Como tanto $k$ quanto $b-k$ já estão dentro do intervalo canônico do resto, seus
restos são eles mesmos:

```math
\begin{aligned}
0\lt k\lt b &\implies \text{mod}(k,b)=k \\
0\lt b-k\lt b &\implies \text{mod}(b-k,b)=b-k \\
\text{mod}(k,b)+\text{mod}(b-k,b) &= k+(b-k)=b.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModSum::sumSymmetricalMods
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModSum.scala). O trecho de código-fonte
está incluído no [Apêndice A.2](#a2-symmetrical-modulo-pairs-excerpt).

<a id="613-unit-step-modulo-division-increment-law"></a>

### 6.13 Lei de Incremento Módulo-Divisão por Passo Unitário

Ao incrementar um número em um, o módulo percorre o ciclo de 0 a b-1 e reinicia,
enquanto a divisão só incrementa quando o módulo atinge seu valor máximo. Isso
captura o comportamento de "vai um" da divisão durante a contagem.

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
```

Sejam $q=\text{div}(a,b)$ e $r=\text{mod}(a,b)$, de modo que $a=bq+r$ com
$0\leq r<b$. Se $r=b-1$, adicionar um produz o estado canônico $(q+1,0)$. Caso
contrário, $r<b-1$, então $(q,r+1)$ já é canônico. Isso também cobre $b=1$:
apenas o primeiro caso pode ocorrer.

```math
\begin{aligned}
r=b-1 &\implies a+1=bq+(b-1)+1=b(q+1)+0 \\
r\lt b-1 &\implies a+1=bq+(r+1),\quad 0\leq r+1\lt b.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Esta propriedade é verificada em [
  ModOperations::addOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala#addOne).

<a id="614-consecutive-integers-zero-density"></a>

### 6.14 Inteiros Consecutivos: Densidade de Zeros

Em qualquer bloco de $p$ inteiros consecutivos, exatamente um é divisível por
$p$. Esta é a forma básica de contagem da periodicidade modular: à medida que
avançamos por inteiros consecutivos, o resto módulo $p$ visita zero uma vez por
período completo.

**No máximo um zero por bloco.** Se $\text{mod}(a,p)=0$ e $0 < d < p$, então
$\text{mod}(a+d,p)\neq 0$. Dentro de qualquer bloco de tamanho $p$ que começa em
um múltiplo, nenhum deslocamento posterior dentro do mesmo bloco também pode ser
divisível por $p$.

```math
\begin{aligned}
\text{mod}(a,\; p) = 0 \;\land\; 0 < d < p &\implies \text{mod}(a + d,\; p) \neq 0
  &&\text{[nonzeroAfterZero]}
\end{aligned}
```

**Pelo menos um zero por bloco.** Para qualquer valor inicial $n$ e módulo
$p>1$, existe um $k \in [0,p)$ tal que $\text{mod}(n+k,p)=0$. A testemunha é
$k=0$ quando $n$ já é divisível por $p$, e $k=p-\text{mod}(n,p)$ caso
contrário.

```math
\begin{aligned}
\forall n \geq 0,\; p > 1,\; \exists\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0
  &&\text{[existsZero]}
\end{aligned}
```

**Exatamente um zero por bloco.** A existência fornece um deslocamento zero,
enquanto a unicidade diz que dois deslocamentos zero no mesmo bloco devem ser
iguais. Juntas, essas afirmações dizem que, entre $p$ inteiros consecutivos a
partir de $n$, exatamente um é divisível por $p$.

```math
\begin{aligned}
\forall n \geq 0,\; p > 1,\;
\exists!\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0
  &&\text{[existsZero + atMostOneZero]}
\end{aligned}
```

Mais explicitamente, seja $k$ o deslocamento fornecido pela existência. Se $i$ e
$j$ são dois deslocamentos em $[0,p)$ com resto zero, o resultado de no máximo
um aplicado a $i$ e $j$ produz $i=j$; logo o $k$ existente é único.

```math
\begin{aligned}
&\exists\, k\in[0,p):\ \text{mod}(n+k,p)=0 \\
&\text{mod}(n+i,p)=\text{mod}(n+j,p)=0,\quad i,j\in[0,p)
  \implies i=j \\
&\therefore\ \exists!\, k\in[0,p):\ \text{mod}(n+k,p)=0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

Essas propriedades são verificadas em [
  ConsecutiveIntegers::nonzeroAfterZero
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala), [
  ConsecutiveIntegers::existsZero
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala), [
  ConsecutiveIntegers::exactlyOneZeroInConsecutive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala), and [
  ConsecutiveIntegers::atMostOneZero
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala).
O formato compacto do código-fonte está incluído no [Apêndice A.3](#a3-consecutive-zero-density-excerpt).
O código-fonte mantido é [
  ConsecutiveIntegers.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala).
O arquivo também contém auxiliares de densidade multifatorial, como
`twoFactorsDensity` e `densityForFactorList`; seus enunciados não são
estabelecidos neste artigo, e a extensão de densidade multiplicativa que eles
visam é discutida como direção aberta em [Trabalho Futuro](#8-future-work).

## 7. Conclusão

Este artigo estabeleceu uma teoria de propriedades formalmente verificada para
divisão e módulo gerada por normalização recursiva de quociente-resto. Dentro
dos domínios declarados, os resultados a seguir mostram que a normalização é
canônica e satisfaz as leis algébricas e periódicas esperadas:

```math
\begin{aligned}
& \forall \text{ } a, b \in \mathbb{N} : b \neq 0 \\
& a < b \implies a \text{ mod } b & = a &&\text{[Trivial Case]} \\
& a < b \implies a \text{ div } b & = 0 &&\text{[Trivial Case]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} : n & \neq 0 \\
n \text{ mod } n & = 0 &&\text{[Identity]} \\
n \text{ div } n & = 1 &&\text{[Identity]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} & : \\
n \text{ mod } 1 & = 0 &&\text{[Division by One]} \\
n \text{ div } 1 & = n &&\text{[Division by One]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : a \geq 0,\; b > 0 \\
a \text{ mod } b & = a \mathbin{\%} b &&\text{[Native Modulo Compatibility]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + b, b) & = \text{mod}(a, b) &&\text{[Linear Shift]} \\
\text{div}(a + b, b) & = \text{div}(a, b) + 1 &&\text{[Linear Shift]} \\
\text{mod}(a - b, b) & = \text{mod}(a, b) &&\text{[Linear Shift]} \\
\text{div}(a - b, b) & = \text{div}(a, b) - 1 &&\text{[Linear Shift]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall a,b,q,r,m \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + m \cdot b, b) & = \text{mod}(a, b) &&\text{[Linear Shift by Multiplier]} \\
\text{div}(a + m \cdot b, b) & = \text{div}(a, b) + m &&\text{[Linear Shift by Multiplier]} \\
\text{mod}(a - m \cdot b, b) & = \text{mod}(a, b) &&\text{[Linear Shift by Multiplier]} \\
\text{div}(a - m \cdot b, b) & = \text{div}(a, b) - m &&\text{[Linear Shift by Multiplier]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a,b,q_x,r_x,q_y,r_y & \in \mathbb{N},\; b \neq 0,\; a = bq_x + r_x = bq_y + r_y \\
DivMod(a,b,q_x,r_x).\text{solve} & = DivMod(a,b,q_y,r_y).\text{solve} &&\text{[Unique Remainder]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b &&\text{[Modulo Idempotence]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b &&\text{[Distributivity, Addition]} \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b &&\text{[Distributivity, Addition]} \\
( a +  c) \text{ mod } b & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) &&\text{[Distributivity, Addition]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b &&\text{[Distributivity, Subtraction]} \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b &&\text{[Distributivity, Subtraction]} \\
( a - c ) \text{ mod } b & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) &&\text{[Distributivity, Subtraction]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a + c ) \text{ mod } b = c \text{ mod } b &&\text{[Divisible-Base Shift Invariance]} \\
\end{aligned}
```
```math
\begin{aligned}
b &> 0,\quad 0 < k < b \\
k \text{ mod } b + (b - k) \text{ mod } b & = b &&\text{[Symmetrical Modulo Pairs]}
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 &&\text{[Unit-Step Increment]} \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 &&\text{[Unit-Step Increment]} \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 &&\text{[Unit-Step Increment]} \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b &&\text{[Unit-Step Increment]} \\
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } n, p & \in \mathbb{N} : p > 1 \\
\exists!\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0 &&\text{[Exactly One Zero per Block]} \\
\end{aligned}
```

Essas propriedades formalmente verificadas estão reunidas em [Summary.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/Summary.scala) e são sustentadas pelos módulos individuais de prova ligados acima. A formulação
recursiva torna a estrutura da prova transparente: normalize $(q,r)$ sem alterar
$a=bq+r$, extraia quociente e resto do estado final, e então derive as leis
algébricas a partir dessa forma normal.
 
Em conjunto, o teorema da solução canônica, as leis de deslocamento, as
identidades aritméticas, a transição por passo unitário e o resultado de um zero
por período caracterizam tanto o estado quociente-resto normalizado quanto seu
comportamento periódico sobre inteiros consecutivos.

<a id="8-future-work"></a>

## 8. Trabalho Futuro

O argumento de normalização recursiva usado ao longo deste artigo generaliza
para além dos inteiros: o mesmo invariante de deslocar e verificar se aplica a
qualquer domínio euclidiano equipado com uma medida bem fundada de resto,
sugerindo um teorema de divisão recursiva mais geral. Os resultados de densidade
de zeros da [Seção 6.14](#614-consecutive-integers-zero-density) também sugerem
uma extensão multiplicativa natural: quando um bloco de inteiros consecutivos é
filtrado por vários módulos coprimos dois a dois, espera-se que a densidade
resultante seja o produto das densidades individuais de módulo único, no espírito
do Teorema Chinês dos Restos [[1]](#ref1). Formalizar essa extensão
multiplicativa e conectar o estado recursivo $DivMod$ à aritmética de classes de
congruência de modo mais amplo são próximos passos naturais a partir das
identidades estabelecidas aqui.

## Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hardy, G. H. and Wright, E. M. (1979). *An Introduction to the Theory of
Numbers* (5th ed.). Clarendon Press, Oxford. Ver a Seção 5.4 para o Teorema
Chinês dos Restos.

## 9. Apêndice

### A.1 Trecho da Propriedade de Identidade

Fonte: [
  ModIdentity.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModIdentity.scala).

```scala
def modIdentity(a: BigInt): Boolean = {
  require(a != 0)
  Calc.mod(a, a) == 0 && Calc.div(a, a) == 1
}.holds
```

<a id="a2-symmetrical-modulo-pairs-excerpt"></a>

### A.2 Trecho dos Pares Simétricos de Módulo

Fonte: [
  ModSum.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModSum.scala).

```scala
def sumSymmetricalMods(b: BigInt, step: BigInt): Boolean = {
  require(b > 0)
  require(step > 0)
  require(step < b)
  assert(Calc.mod(step, b) == step)
  assert(Calc.mod(b - step, b) == b - step)
  assert(Calc.mod(step, b) + Calc.mod(b - step, b) == step + b - step)
  Calc.mod(step, b) + Calc.mod(b - step, b) == b
}.holds
```

<a id="a3-consecutive-zero-density-excerpt"></a>

### A.3 Trecho da Densidade de Zeros Consecutivos

Fonte: [
  ConsecutiveIntegers.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala).

```scala
def nonzeroAfterZero(a: BigInt, p: BigInt, d: BigInt): Boolean = {
  require(p > 1)
  require(a >= 0)
  require(d > 0)
  require(d < p)
  require(Calc.mod(a, p) == 0)

  ModOperations.modAdd(a, p, d)
  ModIdempotence.modIdempotence(d, p)
  ModSmallDividend.modSmallDividend(d, p)

  Calc.mod(a + d, p) != 0
}.holds

def existsZero(n: BigInt, p: BigInt): Boolean = {
  require(p > 1)
  require(n >= 0)

  val r = Calc.mod(n, p)

  if (r == 0) {
    Calc.mod(n, p) == 0
  } else {
    val k = p - r
    ModOperations.modAdd(n, p, k)
    ModSmallDividend.modSmallDividend(k, p)
    Calc.mod(n + k, p) == 0
  }
}.holds

def atMostOneZero(n: BigInt, p: BigInt, i: BigInt, j: BigInt): Boolean = {
  require(p > 1)
  require(n >= 0)
  require(i >= 0 && i < p)
  require(j >= 0 && j < p)
  require(Calc.mod(n + i, p) == 0)
  require(Calc.mod(n + j, p) == 0)

  val smaller = if (i <= j) i else j
  val larger  = if (i <= j) j else i
  val d       = larger - smaller
  assert(d >= 0 && d < p)

  if (d > 0) {
    nonzeroAfterZero(n + smaller, p, d)
  }

  i == j
}.holds
```

### A.4 Log de Verificação

O log de verificação do projeto está disponível em [logs/verify-ch-2-v1-chapter2-_.log](https://github.com/thiagomata/prime-numbers/blob/modulo-article-v1.0.1/logs/verify-ch-2-v1-chapter2-_.log).
