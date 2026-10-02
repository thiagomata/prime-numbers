# Produção Relaxada de Quase-Primos em Sequências de Peneira

**Status da prova:** A base da Sequência de Peneira é verificada em Stainless no
artigo companheiro do capítulo; os resultados algébricos introduzidos aqui são
provados matematicamente. As novas propriedades ainda não são verificadas em
Stainless.

**Autor:** Thiago Henrique Ramos da Mata
Pesquisador Independente
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)<br>
**DOI:** [10.5281/zenodo.22955792](https://doi.org/10.5281/zenodo.22955792)

## Resumo

<div align="justify">
<p style="text-align: justify">

A Sequência de Peneira segura pelo quadrado certifica que todo sobrevivente
$p\in[Q,Q^2)$ é primo. Exigir que $p+2$ sobreviva aos mesmos filtros pediria
um par de primos gêmeos. Em vez disso, estudamos um alvo deliberadamente mais
fraco: exigir que $p+2$ evite primos abaixo de $z=Q^{2\alpha}$ para algum
$\alpha>1/3$ fixo. A positividade então implica que $p+2$ tem no máximo dois
fatores primos para todo $Q$ suficientemente grande.

Provamos três resultados algébricos exatos para esse peso relaxado. A contagem
de um divisor tem um fator local explícito e um resto periódico de fronteira.
O resto natural de divisor, pré-peneirado, é exatamente uma discrepância de
primos na progressão $-2$ módulo $d$. Por fim, o peso final centrado por escalar
se decompõe em produtos de caracteres não principais $\chi(m)\chi(n)$. Um
caractere quadrático módulo $3$ se correlaciona com a contagem relaxada completa
de sobreviventes na roda reduzida completa, refutando o atalho de que o
centramento por densidade escalar cria ortogonalidade Tipo-II com coeficientes
arbitrários.

Esses resultados não provam a positividade do peso relaxado. Eles identificam
sua comparação Tipo-I correta, refutam uma formulação Tipo-II forte demais e
isolam a necessidade restante de um teorema médio para progressões de primos
seguido por uma estimativa bilinear localmente adaptada.

</p>
</div>

<a id="1-introduction"></a>

## 1. Introdução

O programa dos primos gêmeos exige que ambos os extremos sobrevivam a todo
filtro primo ausente abaixo de uma cabeça futura. Este artigo investiga um
programa distinto e mais fraco: o primeiro extremo é primo seguro pelo quadrado,
enquanto o extremo deslocado só precisa evitar primos abaixo de um limiar menor.
A conclusão é um primo mais um inteiro com no máximo dois fatores primos, não um
par de primos gêmeos.

A prova desenvolve os seguintes resultados em ordem de dependência:

1. a positividade do peso relaxado implica produção de primo-mais-$P_2$ — §3;
2. o fator local exato de divisor e o resto periódico — §4;
3. a discrepância exata de progressão de primos para divisor deslocado — §5;
4. a decomposição bilinear exata por caracteres — §6; e
5. o atalho Tipo-II de densidade escalar refutado — §7.

As Seções 8--9 declaram o programa analítico restante e a fronteira exata das
afirmações. Nenhuma identidade de período completo é usada como substituta para
um teorema médio de distribuição em intervalos curtos.

<a id="11-scope-and-evidence-status"></a>

### 1.1 Escopo e Status da Evidência

Seja $Q$ uma cabeça prima e defina

```math
X=Q^2,
\qquad
W=P(Q)=\prod_{p\lt Q}p.
```

Os sobreviventes da roda instalada no intervalo seguro pelo quadrado são

```math
S_Q
=
\{n\in[Q,Q^2):\gcd(n,W)=1\}.
```

Todo $n\in S_Q$ é primo: se fosse composto e menor que $Q^2$, teria um divisor
primo menor que $Q$.

Não provamos aqui um novo teorema de existência. A teoria clássica de Chen já
fornece infinitos primos $p$ para os quais $p+2$ tem no máximo dois fatores
primos. A pergunta específica do projeto é se a positividade pode ser derivada
dos próprios pesos relaxados da Sequência de Peneira.

Provamos matematicamente a implicação em §3 e as propriedades de fator local de
divisor, discrepância de progressão do cofator e obstrução por caracteres
bilineares em §§4--6; nenhuma das quatro ainda é verificada em Stainless.
Nenhuma afirmação neste artigo deve ser descrita como formalmente verificada.

A construção mantida da Sequência de Peneira é verificada em Stainless no
artigo companheiro do capítulo. Este artigo usa essa construção como entrada,
mas não chama suas novas propriedades de teoria dos números de verificadas.
Cada seção de propriedade abaixo declara sua população e seu escopo antes da
prova, e inclui ao final um link para sua nota suplementar de trabalho.

<a id="12-relation-to-known-results"></a>

### 1.2 Relação com Resultados Conhecidos

Este artigo não reprova o teorema de Chen [[7]](#ref7), que já estabelece
infinitos primos $p$ tais que $p+2$ tem no máximo dois fatores primos. A
maquinaria invocada abaixo é padrão na literatura da peneira linear: a sequência
peneirada e a estrutura de nível de distribuição de Halberstam e Richert
[[8]](#ref8), com a terminologia Tipo-I/Tipo-II como em Iwaniec e Kowalski
[[9]](#ref9) e Friedlander e Iwaniec [[10]](#ref10). O que é específico do
projeto é a população: o intervalo seguro pelo quadrado $[Q,Q^2)$ ancorado na
cabeça, as rodas aninhadas $2 \mid Z \mid W$ e a sequência deslocada
pré-peneirada $\mathcal A_Q=\{n+2:n\in S_Q\}$. A obstrução módulo $3$ provada
em §7 é uma correlação específica de caractere fixo na roda reduzida completa; a
barreira clássica da paridade — a incapacidade geral de uma peneira distinguir
a paridade do número de fatores primos — é o contexto mais amplo de por que tais
obstruções locais derrotam modelos de densidade escalar, mas as duas afirmações
não são idênticas e não são confundidas aqui.

<a id="2-preliminaries-and-the-relaxed-candidate-weight"></a>

## 2. Preliminares e o Peso Relaxado Candidato

O vocabulário de peneira usado ao longo do texto:

- Um **número $P_2$** é um inteiro positivo $n$ com
  $\Omega(n)\le2$, onde $\Omega$ conta fatores primos com multiplicidade.
- Uma **peneira de limite inferior** é um método de peneira que produz um
  limite inferior para a contagem de elementos de uma sequência que sobrevivem a
  um conjunto de condições de divisibilidade; a quantidade
  $\sum_{Q\le n\lt Q^2}a_Q(n)$ deste artigo é a soma peneirada que tal método
  limitaria inferiormente.
- Uma **estimativa Tipo-I** controla somas de divisores: ela limita
  $\sum_d \tau(d)\,\bigl|A_d - A_1/\varphi(d)\bigr|$ para divisores $d$ até
  algum nível $D$, isto é, usa distribuição da sequência em progressões
  aritméticas. Para este artigo, os restos relevantes são as discrepâncias de
  progressão de primos de §5.
- Uma **estimativa Tipo-II** controla somas bilineares
  $\sum_{m,n}\xi_m\kappa_n\,a_{mn}$ com coeficientes limitados arbitrários,
  isto é, distribuição da sequência ao longo de produtos; §6 identifica os
  modos exatos de caracteres que tal estimativa precisa controlar para este
  peso.

Escolha um expoente fixo

```math
\frac13\lt\alpha\lt\frac12
```

e defina

```math
z=X^\alpha=Q^{2\alpha},
\qquad
Z=P(z).
```

A restrição superior $\alpha\lt 1/2$ é útil porque dá $z\lt Q$, portanto
$Z\mid W$. Defina

```math
a_Q(n)
=
\mathbf1_{\gcd(n,W)=1}
\mathbf1_{\gcd(n+2,Z)=1}.
```

A candidata pergunta se, para algum $\alpha>1/3$ fixo e infinitas cabeças $Q$,

```math
\sum_{Q\le n\lt Q^2}a_Q(n)>0.
```

Isso é mais fraco do que a positividade de primos gêmeos porque $n+2$ não
precisa sobreviver a todo primo abaixo de $Q$.

<a id="3-relaxed-positivity-implies-prime-plus-almost-prime-production"></a>

## 3. Positividade Relaxada Implica Produção de Primo-Mais-Quase-Primo

**Teorema 1 (A positividade relaxada implica produção de primo-mais-$P_2$).**
Para todo expoente fixo $1/3\lt\alpha\lt1/2$ e toda cabeça futura prima $Q$
suficientemente grande, sobre os inteiros no intervalo seguro pelo quadrado
dessa cabeça ponderados por $a_Q$:

```math
a_Q(n)=1
\quad\Longrightarrow\quad
n\text{ é primo e }\Omega(n+2)\le2.
```

A implicação em si é provada; a positividade para infinitas cabeças permanece
aberta, e nem esta implicação nem as propriedades das quais ela depende são
ainda verificadas em Stainless.

O peso relaxado mantém filtragem suficiente para certificar o primeiro extremo
como primo e para limitar a profundidade de fatoração do segundo. Ele não
certifica o segundo extremo como primo.

Suponha $a_Q(n)=1$ para algum $Q\le n\lt Q^2$. Pelo fator da roda instalada,
$\gcd(n,W)=1$, então a certificação segura pelo quadrado prova que $n$ é primo.
Pelo fator relaxado, $\gcd(n+2,P(z))=1$, então todo fator primo de $n+2$ é pelo
menos $z=X^\alpha$.

Como $3\alpha>1$, existe $X_0(\alpha)$ tal que $X^{3\alpha}>X+1$ sempre que
$X\ge X_0(\alpha)$. Se $n+2$ tivesse pelo menos três fatores primos contados
com multiplicidade, então

```math
\begin{aligned}
\Omega(n+2)\ge3
&\Longrightarrow n+2\ge z^3
&&[\text{Limite Inferior de Três Fatores}]\\
&=X^{3\alpha}
&&[\text{Pela Definição de }z]\\
&>X+1
&&[\text{Pois }3\alpha>1\text{ e }X\ge X_0(\alpha)].
\end{aligned}
```

Por outro lado,

```math
\begin{aligned}
n\lt Q^2=X
&\Longrightarrow n\le X-1
&&[\text{Limite Inteiro}]\\
&\Longrightarrow n+2\le X+1.
&&[\text{Adição de }2]
\end{aligned}
```

As desigualdades se contradizem. Portanto

```math
a_Q(n)=1
\Longrightarrow
n\text{ é primo e }\Omega(n+2)\le2.
\qquad\blacksquare\ \text{[C.Q.D.]}
```

Consequentemente,

```math
\sum_{Q\le n\lt Q^2}a_Q(n)>0
\Longrightarrow
\exists n:\ n\text{ primo e }\Omega(n+2)\le2.
```

Isso é produção de primo-mais-quase-primo. Não é nem um certificado de primos
gêmeos nem uma prova de que a soma relaxada é positiva para alguma família
ilimitada de cabeças.

A candidata específica do projeto e esta prova condicional também estão
registradas, com a mesma derivação, em
[Chen-Type Almost-Prime Survivor](https://github.com/thiagomata/prime-numbers/blob/master/candidates/chen-type-almost-prime-survivor.md). A prova da entrada do primeiro extremo
também está registrada em [Safe-Window 2-Gaps Certify Twin Primes](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md).
Nem essa entrada nem o argumento de contagem de fatores acima estão ainda
codificados como um teorema `.holds`.

<a id="4-exact-divisor-local-factor-and-boundary-remainder"></a>

## 4. Fator Local Exato de Divisor e Resto de Fronteira

**Teorema 2 (Fator local exato de divisor e resto de fronteira).**
Para todo par de rodas primas livres de quadrados $W,Z$ com $2\mid W$, todo
intervalo inteiro $[L,U)$ com $L\lt U$ e todo $m\ge1$, sobre inteiros de peso
relaxado nesse intervalo que também são divisíveis pelo inteiro fixo $m$:

```math
\mathcal N_m[L,U)=\rho(m)\ell_m+E_m[L,U),
\qquad
|E_m[L,U)|\le R-1.
```

Antes de estudar médias de divisores, a densidade de comparação precisa levar
em conta como o divisor testado encontra as duas rodas. Sejam $W$ e $Z$ livres
de quadrados com $2\mid W$, e defina

```math
\mathcal N_m[L,U)
=
\#\{n\in[L,U):m\mid n,\ \gcd(n,W)=1,\ \gcd(n+2,Z)=1\}.
```

Escrever $n=mk$ converte o intervalo numérico em

```math
K_m[L,U)
=
\left[
\left\lceil\frac Lm\right\rceil,
\left\lceil\frac Um\right\rceil
\right)\cap\mathbb Z,
\qquad
\ell_m=|K_m[L,U)|.
```

Se $\gcd(m,W)>1$, escolha um primo $p\mid\gcd(m,W)$. Todo $n=mk$ então tem
$p\mid n$ e não pode ser coprimo a $W$. Assim

```math
\mathcal N_m[L,U)=0.
```

Adote a convenção $\rho(m)=E_m[L,U)=0$ sempre que $\gcd(m,W)>1$: com essa
convenção, a identidade exibida
$\mathcal N_m[L,U)=\rho(m)\ell_m+E_m[L,U)$ vale trivialmente neste ramo, de
modo que o quantificador do teorema sobre todo $m\ge1$ é exato, em vez de ficar
implicitamente restrito ao caso coprimo desenvolvido abaixo.

Agora suponha $\gcd(m,W)=1$. Para todo primo $p\mid WZ$, seja
$\lambda_p(m)$ a contagem dos resíduos permitidos de $k$ módulo $p$. A análise
local direta dá

```math
\lambda_p(m)=
\begin{cases}
p-1,&p\mid W,\ p\nmid Z,\\
1,&p=2,\ p\mid W,\ p\mid Z,\\
p-2,&p>2,\ p\mid W,\ p\mid Z,\\
p,&p\mid Z,\ p\nmid W,\ p\mid m,\\
p-1,&p\mid Z,\ p\nmid W,\ p\nmid m.
\end{cases}
```

Cada linha segue de uma contagem exata de resíduos:

- Se $p\mid W$ e $p\nmid Z$, a hipótese $\gcd(m,W)=1$ torna $m$ invertível
  módulo $p$. A condição instalada proíbe apenas $k\equiv0\pmod p$, deixando
  $p-1$ classes.
- Se $p\mid W$ e $p\mid Z$, as duas condições proíbem
  $k\equiv0\pmod p$ e $k\equiv-2m^{-1}\pmod p$. Elas coincidem para $p=2$,
  deixando uma classe, e são distintas para $p>2$, deixando $p-2$ classes.
- Se $p\mid Z$ e $p\nmid W$, então $p$ é ímpar porque $2\mid W$. Quando
  $p\mid m$, tem-se $mk+2\equiv2\not\equiv0\pmod p$ para todo $k$, então todas
  as $p$ classes sobrevivem. Quando $p\nmid m$, a invertibilidade de $m$ deixa
  exatamente uma classe proibida e, portanto, $p-1$ classes permitidas.

Esses casos são exaustivos porque todo primo que divide $WZ$ pertence apenas à
roda instalada, às duas rodas, ou apenas à roda relaxada. Isso prova a tabela
local.

Defina

```math
R=\prod_{p\mid WZ}p,
\qquad
\rho(m)=\prod_{p\mid WZ}\frac{\lambda_p(m)}p.
```

O CRT prova que todo bloco completo de $R$ valores consecutivos de $k$ contém
exatamente $R\rho(m)$ valores permitidos.

Seja o intervalo de $k$ de comprimento $\ell_m=qR+s$, com $0\le s\lt R$, e
seja $C_m$ a contagem dos valores permitidos em suas $s$ posições finais. Então

```math
\begin{aligned}
\mathcal N_m[L,U)
&=qR\rho(m)+C_m
&&[\text{Períodos Completos Mais Resto}]\\
&=\rho(m)\ell_m+
\left(C_m-s\rho(m)\right).
&&[\text{Substituição}]
\end{aligned}
```

Definir $E_m[L,U)=C_m-s\rho(m)$ dá

```math
\mathcal N_m[L,U)
=\rho(m)\ell_m+E_m[L,U),
\qquad
|E_m[L,U)|\le s\le R-1.
\qquad\blacksquare\ \text{[C.Q.D.]}
```

No intervalo candidato $Z\mid W$, todos os divisores coprimos a $W$ têm a
mesma densidade

```math
\rho_{Q,z}
=
\frac12
\prod_{2\lt p\lt z}\left(1-\frac2p\right)
\prod_{z\le p\lt Q}\left(1-\frac1p\right).
```

Isso é dimensão de peneira dois abaixo de $z$ e dimensão um de $z$ até $Q$.
O limite pontual exato do resto não é um teorema Tipo-I porque o primorial $R$
é muito maior do que o intervalo seguro pelo quadrado.

Nenhum teorema Scala mantido atualmente modela ambas as rodas livres de
quadrados, todos os cinco casos locais, a composição por CRT e o resto de
intervalo arbitrário; deixamos isso não verificado em vez de representá-lo com
código especulativo. Prová-lo exigiria estabelecer a tabela local um primo por
vez e então usar um lema verificado de produto CRT. A prova matemática completa
também está registrada, com a mesma derivação, em [Relaxed Almost-Prime Weight Has An Exact Divisor Local
Factor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md).

<a id="5-shifted-divisor-discrepancy"></a>

## 5. Discrepância de Divisor Deslocado

**Teorema 3 (A discrepância de divisor deslocado reduz a progressões de primos).**
Para toda roda instalada livre de quadrados $W$ com $2\mid W$, todo divisor
ímpar livre de quadrados $d\mid W$ e o intervalo seguro pelo quadrado $I$:

```math
r_d(I)=A_d(I)-\frac{A_1(I)}{\varphi(d)}
=\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
```

Isso é provado sobre todo intervalo inteiro finito $I=[L,U)$, para
sobreviventes da roda instalada nesse intervalo cujo deslocamento $n+2$ é
restringido por $d$. A redução exata é provada; a estimativa acumulada de
progressões de primos permanece aberta.

A peneira de limite inferior deve ser aplicada antes do passo final de filtragem
relaxada. Sua sequência base é

```math
\mathcal A_Q=\{n+2:n\in S_Q\}.
```

Para um divisor ímpar livre de quadrados $d\mid W$, defina

```math
A_d(I)
=
\#\{n\in I:\gcd(n,W)=1,\ d\mid n+2\},
\qquad
A_1(I)=\#\{n\in I:\gcd(n,W)=1\}.
```

Em um sistema completo de resíduos módulo $W$, todo primo que divide $d$ fixa
$n=-2$, enquanto todo outro primo da roda permite todas as classes não nulas.
Portanto

```math
\begin{aligned}
A_d([a,a+W))
&=\prod_{\substack{p\mid W\\p\nmid d}}(p-1)
&&[\text{CRT}]\\
&=\frac{\varphi(W)}{\varphi(d)}
&&[\text{Produtos Livres de Quadrados}]\\
&=\frac{A_1([a,a+W))}{\varphi(d)}.
&&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Assim, a palavra centrada

```math
h_d(n)
=
\mathbf1_{\gcd(n,W)=1}
\left(\mathbf1_{d\mid n+2}-\frac1{\varphi(d)}\right)
```

é $W$-periódica com média zero. Para todo intervalo $I$,

```math
r_d(I)
:=
A_d(I)-\frac{A_1(I)}{\varphi(d)}
```

é exatamente a soma de $h_d$ sobre o único resto incompleto da roda após a
remoção dos blocos completos. Mais explicitamente, escreva

```math
|I|=qW+t,
\qquad
0\le t\lt W.
```

Particione $I$ a partir de seu extremo esquerdo em $q$ blocos completos
consecutivos de comprimento $W$ e um bloco final de comprimento $t$. A
periodicidade e a identidade da roda completa dão

```math
\begin{aligned}
r_d(I)
&=\sum_{n\in I}h_d(n)
&&[\text{Pela Definição}]\\
&=\sum_{u=0}^{q-1}\sum_{j=0}^{W-1}h_d(L+uW+j)
  +\sum_{j=0}^{t-1}h_d(L+qW+j)
&&[\text{Decomposição em Blocos}]\\
&=\sum_{j=0}^{t-1}h_d(L+qW+j).
&&[\text{Blocos Completos Têm Média Zero}]
\end{aligned}
```

Como $|h_d(n)|\le1$, a representação exata dá apenas o limite pontual

```math
|r_d(I)|\le t\le W-1.
```

Para um primorial $W$, esse limite de magnitude é grande demais para ser um
teorema Tipo-I; o fato útil é o resto sinalizado exato.

No intervalo seguro pelo quadrado, sobreviventes da roda são primos. Portanto

```math
r_d(I)
=
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
\qquad\blacksquare\ \text{[C.Q.D.]}
```

A entrada Tipo-I ausente é, consequentemente, um teorema médio da forma

```math
\sum_{\substack{d\le D\\d\mid P(z)/2}}
\tau_B(d)
\max_I
\left|
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}
\right|
\ll
\frac{Q^2}{(\log Q)^A},
```

com um intervalo de níveis $D$ e uma família de intervalos fortes o suficiente
para a peneira de limite inferior escolhida. A estimativa exibida é um alvo
aberto, não um teorema deste artigo.

A identidade CRT de período completo e o resto periódico são adequados para
formalização futura. A interpretação por progressões de primos também depende
da certificação segura pelo quadrado. Nenhum teorema mantido atualmente conecta
todas essas peças para $d$ livre de quadrados arbitrário; a desigualdade
analítica acumulada está fora do que foi formalizado de qualquer modo.
A redução matemática completa também está registrada, com a mesma
derivação, em [Relaxed Cofactor
Divisor Sum Is A Prime-Progression Discrepancy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md).

<a id="6-exact-bilinear-character-decomposition"></a>

## 6. Decomposição Bilinear Exata por Caracteres

**Teorema 4 (Decomposição bilinear exata por caracteres).**
Para todo par de rodas aninhadas livres de quadrados $2\mid Z\mid W$, todo par
de fatores com $\gcd(mn,W)=1$, todo domínio finito de fatores $\mathcal D$ e
coeficientes arbitrários $\xi_m,\kappa_n$, o peso relaxado centrado por escalar
em produtos $x=mn$ se decompõe exatamente em produtos de caracteres não
principais $\chi(m)\chi(n)$ como exibido abaixo.

Suponha $2\mid Z\mid W$ e escreva $Z_{\mathrm{odd}}=Z/2$. Condicionalmente a
$\gcd(x,W)=1$, a densidade relaxada da roda completa é

```math
\vartheta_Z
=
\prod_{p\mid Z_{\mathrm{odd}}}
\left(1-\frac1{p-1}\right).
```

Centralize o peso final por

```math
w(x)
=
\mathbf1_{\gcd(x,W)=1}
\left(
\mathbf1_{\gcd(x+2,Z)=1}-\vartheta_Z
\right).
```

Se $\gcd(mn,W)=1$, então $m,n$ são unidades ímpares módulo todo divisor de
$Z_{\mathrm{odd}}$, então $mn+2$ é ímpar. Os termos pares na identidade de
coprimalidade de Möbius desaparecem, enquanto a expansão do produto de Euler
livre de quadrados para $\vartheta_Z$ dá

```math
\begin{aligned}
\mathbf1_{\gcd(mn+2,Z)=1}
&=
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)},\\
\vartheta_Z
&=
\sum_{d\mid Z_{\mathrm{odd}}}\frac{\mu(d)}{\varphi(d)}.
\end{aligned}
```

Subtrair produz a decomposição pontual exata

```math
w(mn)
=
\mathbf1_{\gcd(m,W)=\gcd(n,W)=1}
\sum_{d\mid Z_{\mathrm{odd}}}
\mu(d)
\left(
\mathbf1_{n\equiv-2m^{-1}\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
\right).
```

A ortogonalidade de caracteres no grupo reduzido de resíduos dá

```math
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
=
\frac1{\varphi(d)}
\sum_{\substack{\chi\ (\mathrm{mod}\ d)\\\chi\ne\chi_0}}
\overline{\chi(-2)}\chi(m)\chi(n).
```

Esta é a família bilinear genuína com coeficientes arbitrários. Ela não é
removida por subtrair uma densidade escalar. De fato, para todo domínio finito
de fatores $\mathcal D$ e coeficientes arbitrários $\xi_m,\kappa_n$, a
substituição dá

```math
\begin{aligned}
\sum_{(m,n)\in\mathcal D}\xi_m\kappa_nw(mn)
&=
\sum_{d\mid Z_{\mathrm{odd}}}
\frac{\mu(d)}{\varphi(d)}
\sum_{\substack{\chi\ (\mathrm{mod}\ d)\\\chi\ne\chi_0}}
\overline{\chi(-2)}\\
&\qquad\cdot
\sum_{\substack{(m,n)\in\mathcal D\\
\gcd(m,W)=\gcd(n,W)=1}}
\xi_m\kappa_n\chi(m)\chi(n).
&&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

A fórmula diagonaliza os modos locais de congruência. Ela não os estima: a
geometria de $\mathcal D$, por exemplo uma restrição hiperbólica sobre $mn$,
ainda acopla as duas variáveis.

A prova usa inversão de Möbius e ortogonalidade finita de caracteres, nenhuma
das quais atualmente tem uma representação em Stainless para este peso no
projeto. A álgebra finita exata é provada matematicamente acima e também
registrada, com a mesma derivação, em [Relaxed Almost-Prime Bilinear
Remainder Has A Character Obstruction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md).

<a id="7-refuted-route--scalar-density-type-ii-orthogonality"></a>

## 7. Rota Refutada — Ortogonalidade Tipo-II por Densidade Escalar

**Teorema 5 (A ortogonalidade Tipo-II por densidade escalar falha na roda
completa).** Para todo par de rodas livres de quadrados $2\mid Z\mid W$ com
$3\mid Z$, o caractere quadrático módulo $3$ dá coeficientes de produto
limitados com

```math
\left|
\sum_{m,n\in G_W}\chi_3(m)\chi_3(n)w(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
```

Esta seção refuta uma afirmação auxiliar, usando coeficientes de caracteres
limitados sobre pares de produtos na roda reduzida completa $G_W\times G_W$.
A refutação não toca a candidata #25 em si nem estimativas Tipo-II localmente
adaptadas em domínios curtos.

O atalho fracassado afirmava que o centramento escalar torna o peso da roda
completa ortogonal a todos os coeficientes de produto limitados, ou pelo menos
dá uma contração estrita universal $c\lt1$ relativa à contagem relaxada de
sobreviventes. O caractere quadrático módulo $3$ refuta ambas as afirmações.

Suponha $3\mid Z$. Seja $\chi_3$ o caractere real não principal módulo $3$ e
seja

```math
G_W=(\mathbb Z/W\mathbb Z)^\times.
```

Escolha coeficientes de produto limitados

```math
\xi_m=\chi_3(m),
\qquad
\kappa_n=\chi_3(n).
```

Se o peso relaxado aceita $mn$, então $mn+2$ é não nulo módulo $3$. Como $mn$ é
uma unidade, necessariamente $mn\equiv2\pmod3$, e portanto

```math
\xi_m\kappa_n=\chi_3(mn)=-1.
```

Logo, o indicador relaxado tem correlação

```math
\sum_{m,n\in G_W}\xi_m\kappa_na(mn)
=
-\sum_{m,n\in G_W}a(mn).
\qquad[\text{Sinal Constante do Caractere}]
```

A comparação escalar é

```math
b(x)=\vartheta_Z\mathbf1_{\gcd(x,W)=1}.
```

O CRT equilibra os resíduos reduzidos entre as duas classes de unidades módulo
$3$, então $\sum_{m\in G_W}\chi_3(m)=0$. Como todo produto de duas unidades da
roda é novamente uma unidade da roda,

```math
\begin{aligned}
\sum_{m,n\in G_W}\xi_m\kappa_nb(mn)
&=\vartheta_Z
  \left(\sum_{m\in G_W}\chi_3(m)\right)
  \left(\sum_{n\in G_W}\chi_3(n)\right)
&&[\text{Comparação Escalar}]\\
&=0.
&&[\text{Equilíbrio CRT}]
\end{aligned}
```

Como $w=a-b$, a subtração dá

```math
\left|
\sum_{m,n\in G_W}\xi_m\kappa_nw(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
\qquad\blacksquare\ \text{[C.Q.D.]}
```

Assim, o centramento por densidade escalar não produz ortogonalidade na roda
completa nem qualquer contração universal estrita contra coeficientes de produto
arbitrários: a razão em relação à contagem de sobreviventes é exatamente $1$.

Este contraexemplo não refuta a positividade do peso relaxado. Ele refuta
apenas o atalho de prova que trata o peso periódico final centrado por escalar
como localmente pseudorrandômico. Um domínio hiperbólico curto de fatores não é
uma roda reduzida completa, então o contraexemplo também não decide toda
estimativa Tipo-II localmente adaptada.

A afirmação fracassada exata, o contraexemplo e a fronteira de nova tentativa
estão arquivados em [Scalar-Density Type-II Orthogonality For The Relaxed Weight](https://github.com/thiagomata/prime-numbers/blob/master/candidates/refuted/relaxed-weight-scalar-density-type-ii.md). O mesmo
cálculo de caracteres é derivado da decomposição bilinear por caracteres
provada em §6 acima. Nenhuma amostra empírica é usada na refutação.

<a id="8-the-correct-remaining-program"></a>

## 8. O Programa Restante Correto

Os resultados provados impõem uma ordem ao trabalho restante.

Primeiro, parear um teorema sobre primos em progressões aritméticas com o resto
exato de divisor deslocado

```math
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
```

O teorema precisa cobrir o intervalo de divisores e a uniformidade de intervalos
exigidos pela peneira de limite inferior escolhida. Uma contagem CRT de período
completo não pode substituir essa média.

Segundo, formular Tipo II antes do passo final de peneiramento relaxado, ou usar
uma sequência de comparação que já inclua todo modo local fixo de caractere. O
indicador final centrado por escalar não é um modelo pseudorrandômico admissível.

Terceiro, verificar que os intervalos Tipo-I e bilineares provados de fato
tornam positivo o peso quase-primo de limite inferior. Nem fatores locais nem
fórmulas de ortogonalidade implicam positividade por si só.

<a id="9-claim-boundary"></a>

## 9. Fronteira das Afirmações

Este artigo prova:

1. que a positividade do peso relaxado implica um primo mais um inteiro com no
   máximo dois fatores primos;
2. o fator local exato de um divisor e o resto periódico de fronteira;
3. a redução exata de divisor deslocado a progressões de primos;
4. a família bilinear exata de resíduo inverso e caracteres não principais; e
5. a falha da ortogonalidade Tipo-II por densidade escalar na roda completa.

Ele não prova:

- positividade para alguma família ilimitada de cabeças;
- a estimativa acumulada de progressões de primos;
- uma estimativa Tipo-II localmente adaptada;
- uma nova prova do teorema de Chen; nem
- qualquer afirmação sobre primos gêmeos.

<a id="10-conclusion"></a>

## 10. Conclusão

O programa relaxado tem uma conclusão condicional provada. Para
$1/3\lt\alpha\lt1/2$ fixo e $Q$ suficientemente grande,

```math
a_Q(n)=1
\Longrightarrow
n\text{ é primo e }\Omega(n+2)\le2.
```

A propriedade de fator local de divisor dá a comparação exata de um divisor.
Divisores que compartilham a roda desaparecem; divisores coprimos têm

```math
\begin{aligned}
\mathcal N_m[L,U)
&=\rho(m)\ell_m+E_m[L,U),
&&[\text{Decomposição Exata do Intervalo}]\\
|E_m[L,U)|&\le R-1,
&&[\text{Fronteira Periódica}]\\
\rho_{Q,z}
&=
\frac12
\prod_{2\lt p\lt z}\left(1-\frac2p\right)
\prod_{z\le p\lt Q}\left(1-\frac1p\right).
&&[\text{Especialização de Rodas Aninhadas}]
\end{aligned}
```

A propriedade de discrepância de progressão do cofator identifica exatamente o
resto Tipo-I natural pré-peneirado:

```math
\begin{aligned}
r_d(I)
&=A_d(I)-\frac{A_1(I)}{\varphi(d)}
&&[\text{Discrepância de Divisor Deslocado}]\\
&=\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}.
&&[\text{Identidade Prima Segura pelo Quadrado}]
\end{aligned}
```

A propriedade de obstrução por caracteres bilineares dá o espectro bilinear não
principal exato

```math
\mathbf1_{mn\equiv-2\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
=
\frac1{\varphi(d)}
\sum_{\chi\ne\chi_0}
\overline{\chi(-2)}\chi(m)\chi(n),
```

e o caractere módulo $3$ refuta o centramento apenas escalar:

```math
\left|
\sum_{m,n\in G_W}\chi_3(m)\chi_3(n)w(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
```

O próximo teorema precisa, portanto, acrescentar informação genuína de
distribuição média de primos e usar uma formulação bilinear localmente
adaptada. Mesmo essas duas estimativas ainda precisam ser inseridas em uma
identidade quase-prima de limite inferior que prove positividade. O artigo
estabelece as reduções algébricas e um atalho fracassado; ele não fornece esse
argumento analítico final, uma nova prova do teorema de Chen, nem um resultado
de primos gêmeos.

## Referências

1. [Chen-Type Almost-Prime Survivor](https://github.com/thiagomata/prime-numbers/blob/master/candidates/chen-type-almost-prime-survivor.md).
2. [Relaxed Almost-Prime Weight Has An Exact Divisor Local Factor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md).
3. [Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md).
4. [Relaxed Cofactor Divisor Sum Is A Prime-Progression Discrepancy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md).
5. [Scalar-Density Type-II Orthogonality For The Relaxed Weight](https://github.com/thiagomata/prime-numbers/blob/master/candidates/refuted/relaxed-weight-scalar-density-type-ii.md).
6. [Formal Verification of Sieve Sequence Stages and Their Transitions](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md).

Referências externas:

<a name="ref7" id="ref7" href="#ref7">[7]</a>
Chen, J. R. (1973). On the representation of a larger even integer as the
sum of a prime and the product of at most two primes. *Scientia Sinica*,
16, 157--176.

<a name="ref8" id="ref8" href="#ref8">[8]</a>
Halberstam, H. e Richert, H.-E. (1974). *Sieve Methods*. Academic Press,
London.

<a name="ref9" id="ref9" href="#ref9">[9]</a>
Iwaniec, H. e Kowalski, E. (2004). *Analytic Number Theory*. American
Mathematical Society Colloquium Publications, 53.

<a name="ref10" id="ref10" href="#ref10">[10]</a>
Friedlander, J. e Iwaniec, H. (2010). *Opera de Cribro*. American
Mathematical Society Colloquium Publications, 57.

<a id="appendix-a-evidence-and-verification-status"></a>

## Apêndice A: Status da Evidência e da Verificação

| Resultado | Status matemático | Status em Stainless | Referência cruzada |
|--------|---------------------|------------------|--------------------|
| Positividade relaxada implica primo-mais-$P_2$ | Implicação condicional provada; positividade para infinitas cabeças aberta | Ainda não verificado | [Candidate #25](https://github.com/thiagomata/prime-numbers/blob/master/candidates/chen-type-almost-prime-survivor.md) |
| Fator local exato de divisor | Provado, incluindo todos os cinco casos locais e o resto de intervalo arbitrário | Ainda não verificado | [Divisor Local Factor](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md) |
| Discrepância de divisor deslocado | Redução exata provada; estimativa acumulada de progressões de primos aberta | Ainda não verificado | [Cofactor Progression Discrepancy](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md) |
| Decomposição bilinear por caracteres | Decomposições pontual exata e de domínio arbitrário provadas | Ainda não verificado | [Bilinear Character Obstruction](https://github.com/thiagomata/prime-numbers/blob/master/properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md) |
| Atalho Tipo-II por densidade escalar | [Refutado] na roda reduzida completa; domínios curtos localmente adaptados permanecem abertos | Não aplicável a uma afirmação falsa | [Archived refutation](https://github.com/thiagomata/prime-numbers/blob/master/candidates/refuted/relaxed-weight-scalar-density-type-ii.md) |

A construção operacional da Sequência de Peneira e suas entradas seguras pelo
quadrado são documentadas separadamente em [Formal Verification of Sieve Sequence Stages and
Their Transitions](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md). Os novos resultados aritméticos
neste artigo permanecem matematicamente provados; nenhum tem uma representação
em Stainless.
