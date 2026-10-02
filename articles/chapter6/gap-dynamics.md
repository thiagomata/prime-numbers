# Propriedades Estruturais e Fronteiras Sinalizadas de Lacunas 2 em Sequências de Peneira

**Estado da prova:** A base da sequência é verificada pelo Stainless no
artigo complementar sobre Sequências de Peneira; os teoremas introduzidos aqui são provados
matematicamente neste artigo.<br>
**Autor:** Thiago Henrique Ramos da Mata<br>
Pesquisador independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**Licença:** [CC BY 4.0](../LICENSE)<br>
**DOI:** [10.5281/zenodo.22955786](https://doi.org/10.5281/zenodo.22955786)

## Resumo

<div align="justify">
<p style="text-align: justify">

Este artigo estuda como lacunas 2 evoluem sob filtros primos sucessivos e
torna mais nítida a fronteira entre sobrevivência em período completo e
posicionamento em janela quadrática. Argumentos de CRT em período completo provam que lacunas 2 persistem globalmente:
um primo ímpar entrante remove exatamente duas classes de cópias de cada lacuna 2 antiga.
Essas contagens não forçam um sobrevivente a cair em um intervalo particular
$[Q,Q^2)$.

O argumento completo reduz a sobrevivência a uma única quantidade sinalizada. Uma lei de conservação ponderada e seu
corolário de Cauchy--Schwarz dão um limiar terminal agudo para a energia de excesso prejudicial.
Um argumento fechado de exaustão — envelopes de capacidade, Bessel em período nativo,
cortes fixos e móveis, e o reparo da lacuna de estabilidade — mostra que nenhuma
rota baseada apenas em capacidade sem sinal consegue ultrapassar esse limiar. A nova contribuição é,
portanto, sinalizada e local. No filtro $7$, a ordem exata dos resíduos dá o
limite intervalar agudo $|b_7|\le18/7$, substituindo uma estimativa de capacidade que cresce
quadraticamente com a escala da janela. Mais geralmente, quando um período antigo é
copiado através de um primo entrante $r$, o excesso prejudicial centrado no bloco de cópia
$j$ é exatamente $B_j=d_t+d_{t-2}$ para duas entradas do histograma centrado de
inícios antigos módulo $r$. Consequentemente,
```math
\sum_{j=0}^{r-1}B_j^2
=2V_r+2\sum_{t\bmod r}d_td_{t-2}
\le4V_r.
```

Isso compõe energia de resíduos com o critério ponderado de sobrevivência por excesso prejudicial
sobre blocos completos do período antigo. Não controla os dois fragmentos parciais
de fronteira de um intervalo arbitrário, nem prova uma estimativa relativa de
energia de resíduos ao longo de uma cadeia ilimitada de filtros. Essas são agora as
obrigações aritméticas restantes precisas, enquadradas por um conflito de escala que
limita a média por semente fixa e por uma barreira Tipo-II que qualquer peneira
produtora de primos deve superar.

</p>
</div>

## 1. Introdução

A Sequência de Peneira representa um fluxo infinito de valores aceitos usando uma
lista finita cíclica de lacunas. Essa representação torna exatas as identidades de período completo,
mas a aplicação a primos gêmeos pede um início sobrevivente de lacuna 2 na
janela elegível e segura pelo quadrado de uma cabeça futura. A distinção entre esses
escopos é o princípio organizador deste artigo.

A versão 1 estabeleceu a fronteira entre copiar-ou-mesclar e período completo/janela local.
Esta versão preserva esse eixo teoremático e adiciona os resultados sinalizados
de localização que surgiram da investigação quadrática posterior. O
artigo desenvolve as seguintes propriedades:

1. contagem exata de lacunas 2 em período completo — [§3.1](#31-exact-global-2-gap-count);
2. frequência exata de filtragem por índice de cópia — [§3.2](#32-exact-filter-frequency-across-repeated-copies);
3. sobrevivência exata em lote — [§3.3](#33-exact-batched-2-gap-survival);
4. contagem exata de agrupamentos `(2,4,2)` em período completo — [§3.4](#34-exact-global-242-cluster-count);
5. invariância por rotação das contagens cíclicas — [§3.5](#35-rotation-preserves-cyclic-gap-counts);
6. ausência global estável de lacunas 2 — [§3.6](#36-absence-of-2-gaps-is-stable);
7. certificação segura pelo quadrado — [§4.1](#41-safe-window-2-gaps-certify-twin-primes);
8. isolamento após o filtro 3 — [§4.2](#42-isolation-of-2-gaps-after-filter-3);
9. ataques aceitos exatos e o limiar agudo de uma transição —
   [§§4.3](#43-exact-accepted-local-filter-strikes)--[4.4](#44-sharp-local-2-gap-survival-threshold);
10. por que o envelope de capacidade se esgota — [§6](#6-why-the-capacity-envelope-is-exhausted);
11. conservação ponderada exata de deleções e seu corolário quadrático terminal
    — [§§5.1](#51-weighted-deletion-conservation)--[5.2](#52-terminal-survival-criterion);
12. a economia intervalar exata do filtro $7$ — [§7](#7-exact-filter-seven-localization);
13. a fronteira ativa (estimativas de discrepância na fronteira aceita e de energia de colisão de resíduos) — [§8](#8-open-estimates-and-their-proven-reductions);
14. a ponte entre energia de resíduos e excesso prejudicial por bloco de cópia — [§9](#9-copy-block-harmful-excess-and-residue-energy);
15. as rotas classificadas e o programa ativo — [§10](#10-routes-that-are-now-classified); e
16. o conflito de escala com semente fixa ([§10.1](#101-the-fixed-seed-scale-conflict)) e a barreira Tipo-II ([§11.1](#111-why-this-is-hard-the-type-ii-barrier)).

As seções finais separam o controle provado em blocos completos das estimativas abertas
de fronteira parcial e entre camadas. Nenhum teorema de período completo é usado
como limite inferior para janela curta.

## 2. Preliminares e Fronteira de Evidência

Para uma cabeça prima de estágio $p$, seja
```math
M_p=\prod_{q\lt p}q
```

e retenha os inteiros coprimos com $M_p$. Seus resíduos aceitos se repetem
módulo $M_p$; diferenças adjacentes em um período completo formam uma lista cíclica
de lacunas. O artigo complementar verificado estabelece completude dos valores aceitos,
crescimento estrito, deslocamento de período, contagem exata de sobreviventes e a regra
de transição copiar-ou-mesclar.

Este artigo toma esses fatos verificados de construção como entradas. Em seguida,
estuda propriedades matemáticas de populações de lacunas 2 e discrepâncias intervalares
sinalizadas. A divisão é deliberada: o artigo complementar fixa e
verifica por máquina o objeto da peneira; este artigo expande a teoria matemática
desse objeto sem afirmar que todo novo teorema possui uma codificação em Scala.

### 2.1 Papéis, Populações e Escopos

A notação segue o vocabulário compartilhado da pesquisa:

- $Q$ é uma **cabeça futura** fixa usada para certificação segura pelo quadrado;
- $r$ é um **primo entrante**, e $r_i$ é o filtro $i$ em uma cadeia condicionada completa até $Q$;
- um **período completo** contém um padrão cíclico completo da peneira;
- uma **janela local** é um intervalo inteiro limitado explicitamente declarado;
- uma **população de inícios de lacunas 2** conta inícios $x$, não todos os valores aceitos; e
- um **certificado seguro pelo quadrado** exige que tanto $x$ quanto $x+2$ estejam estritamente
  abaixo de $Q^2$ depois que todo primo ausente abaixo de $Q$ foi instalado.

Para uma cadeia condicionada, $S_i$ denota os inícios locais de lacunas 2 imediatamente
antes do filtro $r_i$, e $N_i=|S_i|$. A população final de sobreviventes é $S_m$
com tamanho $N_m$. Populações de período completo são nomeadas separadamente e
nunca são substituídas por $N_i$ sem um teorema explícito de localização.

### 2.2 Estado da Evidência

Usamos a seguinte convenção de estado:

- **Base verificada:** sustentada por código Stainless mantido no artigo complementar.
- **Aberto:** a estimativa necessária é enunciada, mas não provada.

Todo outro resultado provado neste artigo é provado matematicamente no
próprio texto; as derivações e os apêndices são a autoridade para as
afirmações matemáticas do artigo.

Nenhum teorema neste artigo afirma que existem infinitos primos gêmeos.

Cada seção de propriedade declara sua população, seu escopo e seu quantificador, e então
prova o resultado. Entradas verificadas de construção apontam para contratos Scala mantidos.

<a id="3-complete-period-2-gap-properties"></a>

## 3. Propriedades de Lacunas 2 em Período Completo

O primeiro grupo de propriedades trata de inícios cíclicos de lacunas 2 em períodos completos.
Essas identidades são exatas porque todo primo instalado contribui um sistema completo
de resíduos. Elas não são enunciados sobre uma janela quadrática local.

<a id="31-exact-global-2-gap-count"></a>
### 3.1 Contagem Global Exata de Lacunas 2

Depois que o filtro $2$ é instalado, todo valor aceito é ímpar, portanto os
extremos aceitos $x$ e $x+2$ são sobreviventes consecutivos: o valor intermediário é
par. Para todo estágio primo após o filtro $2$, esta propriedade conta todos esses
inícios cíclicos de lacunas 2 em um período completo daquele estágio, sem
construir a lista de lacunas.

Seja $p$ a cabeça do estágio e
```math
M_p=\prod_{q\lt p}q,
```

onde $q$ varia sobre os primos instalados. Um resíduo $x$ representa uma
lacuna 2 cíclica exatamente quando
```math
\gcd(x(x+2),M_p)=1.
```

A contagem exata é
```math
G_2(p)
=
\prod_{\substack{3\le q\lt p\\q\text{ prime}}}(q-2).
```

Para o filtro $2$, o início deve ser ímpar, deixando um resíduo permitido. Para
cada primo ímpar instalado $q$, os dois extremos falham precisamente nas duas
classes
```math
x\equiv0\pmod q,
\qquad
x\equiv-2\pmod q.
```

Elas são distintas porque $q$ é ímpar, então exatamente $q-2$ resíduos permanecem
permitidos em cada primo ímpar instalado $q$.

Os primos instalados são coprimos dois a dois, então o CRT dá uma bijeção entre
uma escolha permitida em cada primo instalado e um resíduo módulo $M_p$.
Consequentemente,
```math
\begin{aligned}
G_2(p)
&=1\cdot
\prod_{\substack{3\le q\lt p\\q\text{ prime}}}
(q-2)
&&[\text{Teorema Chinês dos Restos}]\\
&=\prod_{\substack{3\le q\lt p\\q\text{ prime}}}(q-2).
&&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

O produto vazio sobre primos ímpares é $1$, então o enunciado inclui o primeiro estágio ímpar.
O resultado prova presença global em período completo, não posicionamento em qualquer
janela local especificada.

A derivação acima prova a contagem exata por produto.

<a id="32-exact-filter-frequency-across-repeated-copies"></a>
### 3.2 Frequência Exata de Filtro em Cópias Repetidas

A expansão distribui toda lacuna 2 antiga por cópias igualmente espaçadas antes da
filtragem, e um primo entrante não pode escolher cópias arbitrárias: os dois
ataques aos extremos ocorrem em duas fases exatas de índice de cópia. Isso vale para
cópias elevadas de uma lacuna 2 cíclica antiga fixa, ao longo de toda execução completa ou finita de
índices de cópia que satisfaça a pré-condição de coprimalidade declarada.

Seja $M$ o período antigo, seja $(a,a+2)$ uma lacuna 2 cíclica antiga, e seja
$r>2$ um primo entrante com $\gcd(M,r)=1$. A cópia $j$ tem extremos
```math
a+jM,
\qquad
a+2+jM.
```

Seja $M^{-1}$ o inverso de $M$ módulo $r$. O extremo esquerdo é
deletado exatamente quando
```math
\begin{aligned}
a+jM&\equiv0\pmod r
&&[\text{Ataque ao Extremo Esquerdo}]\\
j&\equiv-aM^{-1}\pmod r.
&&[\text{Multiplicar por }M^{-1}]
\end{aligned}
```

De modo análogo, o extremo direito é deletado exatamente quando
```math
\begin{aligned}
a+2+jM&\equiv0\pmod r
&&[\text{Ataque ao Extremo Direito}]\\
j&\equiv-(a+2)M^{-1}\pmod r.
&&[\text{Multiplicar por }M^{-1}]
\end{aligned}
```

Se as duas classes de índice de cópia fossem iguais, subtrair daria
$2M^{-1}\equiv0\pmod r$, portanto $2\equiv0\pmod r$, impossível para $r>2$.
Portanto, as classes são distintas.

Toda classe de resíduo módulo $r$ ocorre no máximo $\lceil L/r\rceil$ vezes em uma
execução de $L$ índices de cópia consecutivos. Assim,
```math
K_r(J)\le2\left\lceil\frac{L}{r}\right\rceil.
```

Em uma execução completa de $r$ índices de cópia consecutivos, cada classe proibida
ocorre exatamente uma vez. Logo,
```math
K_r=2,
\qquad
G_{\mathrm{survive}}=r-2.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

Esta é a distribuição exata entre cópias antes e durante um filtro. Ela não
diz que os $r-2$ sobreviventes são distribuídos uniformemente após a filtragem nem
que um deles esteja em uma janela numérica escolhida.

A derivação acima prova esta lei exata de índice de cópia.

<a id="33-exact-batched-2-gap-survival"></a>
### 3.3 Sobrevivência Exata de Lacunas 2 em Lote

A lei de cópias de um filtro compõe exatamente. Aplicar vários filtros futuros como
um lote conta interseções via CRT, de modo que nenhum sobrevivente é subtraído duas vezes
e nenhuma aproximação intermediária por piso ou densidade é necessária. Isso vale para
todo conjunto finito de primos ímpares entrantes distintos e coprimos com o período antigo,
sobre um período completo após o lote inteiro, para cópias elevadas de toda
lacuna 2 cíclica antiga em um período combinado completo.

Seja $M$ o período antigo e seja $(a,a+2)$ uma lacuna 2 cíclica antiga. Escolha um
conjunto finito de primos ímpares distintos
```math
\mathcal R=\{r_1,r_2,\ldots,r_k\},
\qquad
\gcd\!\left(M,\prod_{r\in\mathcal R}r\right)=1,
```

e defina
```math
R=\prod_{r\in\mathcal R}r.
```

O período combinado completo módulo $MR$ contém $R$ cópias elevadas do
par antigo. Exatamente
```math
\prod_{r\in\mathcal R}(r-2)
```

sobrevivem a todos os filtros do lote. Portanto, se o período completo antigo tem
$G$ lacunas 2 cíclicas, o novo período completo tem
```math
G_{\mathrm{after}}
=G\prod_{r\in\mathcal R}(r-2).
```

Para cada $r\in\mathcal R$, o teorema de frequência de filtro ([§3.2](#32-exact-filter-frequency-across-repeated-copies)) identifica duas classes proibidas distintas
de índice de cópia: uma onde $r$ divide o extremo esquerdo e outra onde ele
divide o extremo direito. Portanto, há exatamente $r-2$ escolhas permitidas
módulo $r$. Como os primos em $\mathcal R$ são coprimos dois a dois, o CRT torna
essas escolhas independentes. Assim, para uma lacuna 2 antiga,
```math
\begin{aligned}
G_{\mathrm{one\ old\ gap}}
&=\prod_{r\in\mathcal R}(r-2).
&&[\text{Teorema Chinês dos Restos; Frequência de Filtro por Índice de Cópia}]
\end{aligned}
```

Os conjuntos de cópias elevadas pertencentes a inícios cíclicos antigos distintos são contados como
inícios distintos no novo período completo. Somar a mesma contagem exata sobre
os $G$ inícios antigos dá
```math
\begin{aligned}
G_{\mathrm{after}}
&=\sum_{g=1}^{G}
  \prod_{r\in\mathcal R}(r-2)
&&[\text{Soma sobre Inícios Antigos de Lacunas 2}]\\
&=G\prod_{r\in\mathcal R}(r-2).
&&\blacksquare\ \text{[Simplificação; C.Q.D.]}
\end{aligned}
```

A fórmula independe da ordem conceitual dos filtros e conta corretamente
ataques sobrepostos. Seu escopo, ainda assim, é o período combinado completo
$MR$. Um intervalo mais curto pode omitir todas as classes permitidas pelo CRT, então este
teorema não pode posicionar um sobrevivente em uma janela elegível e segura pelo quadrado.

A derivação acima prova a fórmula de lote finito e sua limitação a período completo.

<a id="34-exact-global-242-cluster-count"></a>
### 3.4 Contagem Global Exata de Agrupamentos `(2,4,2)`

O rótulo $(2,4,2)$ nomeia a sequência de lacunas consecutivas dentro de um
agrupamento de quatro termos
```math
a,\qquad a+2,\qquad a+6,\qquad a+8:
```
lacuna $2$ de $a$ a $a+2$, lacuna $4$ de $a+2$ a $a+6$, e novamente lacuna $2$ de
$a+6$ a $a+8$. Esta é a forma clássica de quadrupleta prima, realizada por
exemplo por $11,13,17,19$ ou $101,103,107,109$: dois pares de primos gêmeos que compartilham
seus dois valores intermediários separados por quatro. Contar quantas vezes esse padrão exato
sobrevive é a próxima pergunta natural depois que lacunas 2 individuais ([§3.1](#31-exact-global-2-gap-count)) são
compreendidas, pois pergunta se lacunas 2 continuam chegando em pares próximos
em vez de apenas individualmente. É também daí que o padrão vem inicialmente:
no estágio mais antigo, logo após a instalação dos filtros $2$ e $3$,
toda a sequência aceita já se repete como $\ldots,2,4,2,4,2,\ldots$
indefinidamente, então $(2,4,2)$ começa como a forma universal da sequência, não
como um evento raro — esta seção acompanha quanto dessa forma sobrevive à medida que primos maiores
a filtram.

As duas lacunas 2 do agrupamento têm extremos disjuntos e ficam em um intervalo total de
$8$. A expansão
cria $r$ cópias de todo agrupamento antigo; o filtro entrante atinge exatamente
quatro cópias e preserva intactas as outras $r-4$.

Seja $C_M$ a contagem cíclica de agrupamentos no módulo $M$. A cópia $j$ de um agrupamento
tem extremos
```math
a+jM+\{0,2,6,8\},
\qquad
0\le j\lt r.
```

Para cada deslocamento $h\in\{0,2,6,8\}$, o extremo $a+jM+h$ é removido exatamente
na classe de índice de cópia
```math
j\equiv-(a+h)M^{-1}\pmod r.
```

Se dois deslocamentos produzissem a mesma classe, sua diferença seria divisível
por $r$. As diferenças não nulas dois a dois são $2,4,6,8$. Nem $5$ nem $7$
divide qualquer diferença aplicável, e todo primo $r\ge11$ excede as quatro.
Assim, as quatro classes são distintas. Das $r$ cópias totais criadas pela
expansão, seja $N_{\text{struck}}$ o número de cópias atingidas pelo
filtro entrante (uma por classe distinta de extremo) e $N_{\text{intact}}$
o número deixado intacto. Então
```math
\begin{aligned}
N_{\text{struck}}&=4
&&[\text{Quatro Classes Distintas de Extremos}]\\
N_{\text{intact}}&=r-N_{\text{struck}}=r-4.
&&[\text{Subtração}]
\end{aligned}
```

Resta excluir agrupamentos recém-criados. Após o filtro $2$, todas as lacunas antigas
são positivas e pares. Uma lacuna mesclada é a soma de pelo menos duas lacunas antigas, então
não pode ser igual a $2$. Ela pode ser igual a $4$ apenas como $2+2$. Mas duas lacunas 2 consecutivas
exigiriam que todos os três valores $x,x+2,x+4$ fossem aceitos, enquanto um deles
é divisível por $3$. Como o filtro $3$ está instalado, isso é impossível.
Portanto, toda nova lacuna de tamanho $2$ ou $4$ é uma lacuna antiga copiada, e toda nova
ocorrência de $(2,4,2)$ é uma das cópias intactas contadas acima. Logo
```math
C_{rM}=(r-4)C_M.

\qquad\blacksquare\ \text{[Nenhuma Nova Ocorrência; C.Q.D.]}
```

Essa recorrência vale para todo estágio de período completo com módulo $M$
divisível por $6$ e todo primo entrante $r\ge5$ com $r\nmid M$, contando
ocorrências cíclicas da palavra de lacunas $(2,4,2)$ em um período completo depois que
os filtros $2$ e $3$ são instalados.

A roda módulo $6$ tem palavra cíclica de lacunas $(4,2)$: resíduos aceitos
$1,5\pmod6$ repetem-se para sempre como $\ldots,4,2,4,2,4,2,\ldots$ antes que qualquer primo
além de $3$ seja instalado. Nesse estágio base, a sequência é *nada além de*
cópias de $(2,4,2)$ uma após a outra, então há exatamente uma ocorrência cíclica de $(2,4,2)$
por período, $C_6=1$ — a recorrência abaixo acompanha como esse
padrão inicialmente universal se dilui, mas nunca é destruído, à medida que primos maiores
são instalados. Iterar a recorrência sobre um conjunto finito
de primos instalados $\mathcal P$ contendo $2$ e $3$ dá
```math
C(\mathcal P)
=
\prod_{\substack{p\in\mathcal P\\p\ge5}}(p-4).
```

A população absoluta de agrupamentos é positiva em todo estágio e cresce sempre que
um primo entrante excede $5$. Sua proporção entre posições aceitas é
multiplicada por $(r-4)/(r-1)\lt1$, então crescimento global não implica que uma
janela curta escolhida contenha um agrupamento.

A derivação acima estabelece a recorrência, o resultado de não criação, o produto fechado
e a fronteira de localização.

<a id="35-rotation-preserves-cyclic-gap-counts"></a>
### 3.5 Rotação Preserva Contagens Cíclicas de Lacunas

A rotação escolhe uma nova origem para a mesma lista cíclica. Ela nem filtra um
valor aceito nem mescla lacunas adjacentes, portanto preserva o número de entradas
com cada valor de lacuna, incluindo $2$, para toda lista cíclica finita não vazia de lacunas,
todo deslocamento de rotação não negativo e todo valor de lacuna $d$. A própria invariância por rotação é provada.

Seja
```math
G=(g_0,g_1,\ldots,g_{T-1}),
\qquad T\ge1,
```

e defina a rotação por deslocamento $j$ por
```math
\text{rot}_j(G)_i
=g_{(i+j)\bmod T}.
```

Para todo valor $d$,
```math
\#\{i: \text{rot}_j(G)_i=d\}
=\#\{i:g_i=d\}.
```

Defina o mapa de índices $\varphi_j(i)=(i+j)\bmod T$. A adição por $j$ módulo
$T$ é inversível, com inversa $\varphi_{-j}(i)=(i-j)\bmod T$. Logo
$\varphi_j$ é uma bijeção de
$\{0,1,\ldots,T-1\}$. Portanto
```math
\begin{aligned}
\#\{i:\text{rot}_j(G)_i=d\}
&=\#\{i:g_{\varphi_j(i)}=d\}
&&[\text{Pela Definição de Rotação}]\\
&=\#\{k:g_k=d\}
&&[\text{Reindexar pela Bijeção }k=\varphi_j(i)]\\
&=\#\{i:g_i=d\}.
&&\blacksquare\ \text{[Renomear o Índice Ligado; C.Q.D.]}
\end{aligned}
```

Tomar $d=2$ prova a invariância exata da contagem cíclica completa de lacunas 2.
A rotação pode alterar qual lacuna segue a cabeça exibida e se uma lacuna
cruza a fronteira fim-início de uma renderização linear. Ela não pode implicar que
uma janela de coordenadas absolutas como $[Q,Q^2)$ contenha o mesmo número de
lacunas 2, porque essa janela não é definida apenas por índices cíclicos.

#### Base de Verificação em Scala e Teorema de Multiplicidade Pendente

A implementação mantida de listas define rotação como `back ++ front`. Suas
propriedades verificadas preservam pertencimento nas duas direções e preservam o
tamanho da lista:
```scala
def assertRotateContainsForward(
  list: List[BigInt], index: BigInt, x: BigInt
): Boolean = {
  require(index >= 0)
  require(list.contains(x))
  // ... verified proof ...
  ListUtils.rotateAt(list, index).contains(x)
}.holds

def assertRotateContainsBackward(
  list: List[BigInt], index: BigInt, x: BigInt
): Boolean = {
  require(index >= 0)
  require(ListUtils.rotateAt(list, index).contains(x))
  // ... verified proof ...
  list.contains(x)
}.holds

def assertRotateSameSize(
  list: List[BigInt], index: BigInt
): Boolean = {
  require(index >= 0)
  // ... verified proof ...
  ListUtils.rotateAt(list, index).size == list.size
}.holds
```

Essas bases são verificadas em [
`RotationProperties::assertRotateContainsForward`,
`assertRotateContainsBackward` e `assertRotateSameSize`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RotationProperties.scala).
Elas estabelecem a operação de rotação e seu comportamento de mesmos elementos/tamanho, mas
pertencimento sozinho não conta entradas duplicadas.

<a id="36-absence-of-2-gaps-is-stable"></a>
### 3.6 A Ausência de Lacunas 2 é Estável

Filtragem posterior pode copiar uma lacuna antiga ou mesclar lacunas antigas consecutivas, mas
não pode criar uma lacuna positiva menor. Assim, uma vez que a população cíclica completa
não contém lacuna 2, nenhum filtro posterior pode recriá-la — um fato que
vale para toda transição de filtro posterior e, portanto, para toda cadeia finita de
transições posteriores, sobre toda lacuna em uma lista cíclica completa de lacunas após o filtro 2.

Sejam $g_0,\ldots,g_{T-1}$ as lacunas cíclicas antigas. Como o filtro $2$ já está
instalado, todo $g_i$ é positivo e par. Sob a hipótese sem lacuna 2,
```math
\forall i,\qquad g_i\ne2
\quad\Longrightarrow\quad
g_i\ge4.
```

Para dois valores que permanecem consecutivos após o próximo filtro, sua nova lacuna
$h$ tem uma de duas formas. Se nenhum valor aceito intermediário foi removido, ela
copia uma lacuna antiga. Se um ou mais valores aceitos intermediários foram removidos,
ela é a soma de pelo menos duas lacunas antigas consecutivas. Portanto
```math
\begin{aligned}
h=g_i
&\Longrightarrow h\ge4
&&[\text{Lacuna Copiada}]\\
h=\sum_{j=u}^{v}g_j,\quad v\ge u+1
&\Longrightarrow h\ge4+4=8.
&&[\text{Lacunas Mescladas}]
\end{aligned}
```

Em ambos os casos $h\ne2$, então
```math
\left(\forall i,\ g_i\ne2\right)
\Longrightarrow
\left(\forall j,\ h_j\ne2\right).

\qquad\blacksquare\ \text{[Exaustão Copiar-ou-Mesclar; C.Q.D.]}
```

Aplicar a mesma implicação indutivamente produz
```math
G_s(2)=0
\Longrightarrow
G_t(2)=0
\qquad\text{for every later stage }t\ge s,
```

onde $G_s(2)$ é a contagem de lacunas 2 em período completo no estágio $s$. Este é um
teorema de extinção em uma direção. Uma contagem global positiva não força uma lacuna 2
a cair em uma janela curta escolhida, portanto ela não deve ser usada como resultado de localização.

O argumento copiar-ou-mesclar acima prova a consequência indutiva e sua
fronteira global/local.

Estes são enunciados de período completo. Eles explicam crescimento global, mas não
localizam qualquer cópia sobrevivente em um intervalo curto prescrito.

A representação verificada em Scala da repetição, filtragem
e reconstrução do próximo estágio subjacentes é documentada em [Formal Verification of Sieve
Sequence Stages and Their Transitions](https://doi.org/10.5281/zenodo.22955782). Este artigo
não duplica essas provas de código-fonte mantidas.

[§§3.1](#31-exact-global-2-gap-count)–[3.6](#36-absence-of-2-gaps-is-stable) acima são identidades exatas de período completo; nenhuma delas mede uma
janela local curta, e a Seção 3.6 alerta explicitamente contra ler uma
contagem global positiva como garantia local. A figura abaixo mostra a
quantidade que esses teoremas deliberadamente não limitam: a fração das lacunas próprias de um
estágio que são iguais a $2$, por estágio, em um conjunto real de dados gerados (200
estágios, as primeiras $100{,}000$ lacunas de cada). Ela cai acentuadamente de $100\%$
(estágio 1, onde toda lacuna apenas ímpar é $2$) para aproximadamente $10\%$ perto da
cabeça $\approx1200$ — consistente com a fórmula de produto de $G_2(p)$ rarefazendo a
contagem de *período completo*, mas mostrada aqui na escala *local, por estágio* que
os teoremas da Seção 3 cuidadosamente não reivindicam.

![Fração das lacunas de um estágio iguais a 2, por estágio, declinando de 100% para cerca de 10%](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-two-frequency.svg)

A figura acima resume cada estágio em um número; a figura abaixo mostra
os mesmos dados subjacentes com detalhe completo por linha, sobre o mesmo conjunto de dados de 200 estágios.
Toda lacuna 2 é renderizada em um verde fixo; tudo entre uma lacuna 2
e a próxima é colapsado em uma única unidade colorida que representa essa
distância. Uma linha majoritariamente verde é um estágio cujas lacunas 2 ainda estão quase
coladas; uma linha com longas sequências coloridas é um estágio em que lacunas 2 se
espalharam. Esta é a textura linha a linha por trás da curva de frequência decrescente
acima, não uma nova afirmação.

![Mapa de calor de compressão focado em 2: toda lacuna 2 em verde, a distância colapsada até a próxima colorida por frequência, uma linha por estágio](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-heatmap-2focused.svg)

## 4. Certificação Local e Sobrevivência de Uma Transição

O crescimento em período completo se torna relevante para primos gêmeos apenas depois que um teorema
posiciona uma lacuna 2 sobrevivente dentro de uma janela elegível e segura pelo quadrado. Esta seção
primeiro prova o que tal sobrevivente certifica, depois isola as condições locais exatas
de atrito necessárias para reter um.

<a id="41-safe-window-2-gaps-certify-twin-primes"></a>
### 4.1 Lacunas 2 em Janela Segura Certificam Primos Gêmeos

O limite quadrático transforma aceitação em primalidade. Todo composto abaixo de $Q^2$
tem um divisor primo abaixo de $Q$, mas todo divisor desse tipo já foi
instalado como filtro. Portanto, para toda cabeça futura prima $Q$ e todo
inteiro aceito $n$ com $Q\le n\lt Q^2$ depois que todos os primos abaixo de $Q$ são
instalados, um par aceito sobrevivente à distância $2$ não é apenas um
par putativo; é um par de primos gêmeos.

Seja
```math
P_Q=\prod_{r\lt Q}r,
```

onde $r$ varia sobre primos. Se
```math
Q\le n\lt Q^2,
\qquad
\gcd(n,P_Q)=1,
```

então $n$ é primo. De fato, suponha que $n$ fosse composto. Ele tem um
divisor primo $r\le\sqrt n$. O limite quadrático estrito dá
$r\le\sqrt n\lt Q$, então $r$ é um dos fatores de $P_Q$. Consequentemente
$r\mid n$ e $r\mid P_Q$, contradizendo $\gcd(n,P_Q)=1$:
```math
\begin{aligned}
n\text{ composite}
&\Longrightarrow
\exists r\text{ prime}:r\mid n\ \land\ r\le\sqrt n
&&[\text{Divisor Primo Pequeno}]\\
&\Longrightarrow r\lt Q
&&[\text{Limite Estrito }n\lt Q^2]\\
&\Longrightarrow r\mid P_Q
&&[\text{Pela Definição}]\\
&\Longrightarrow \gcd(n,P_Q)>1
&&[\text{Como }r\mid n]\\
&\Longrightarrow \bot.
&&[\text{Contradição}]
\end{aligned}
```

Logo $n$ é primo. Aplicar esse resultado independentemente aos dois extremos dá
```math
Q\le x,
\qquad
x+2\lt Q^2,
\qquad
\gcd(x(x+2),P_Q)=1
\Longrightarrow
x\text{ e }x+2\text{ são primos}.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

A desigualdade no extremo direito deve ser estrita: $Q^2$ é composto, mas não tem
divisor primo abaixo de $Q$. O teorema certifica um sobrevivente elegível; ele
não prova que tal sobrevivente existe.

A derivação acima prova o teorema e sua disciplina de extremos.

<a id="42-isolation-of-2-gaps-after-filter-3"></a>
### 4.2 Isolamento de Lacunas 2 Após o Filtro 3

Após o filtro $3$, duas lacunas 2 não podem compartilhar um extremo, para todo estágio da peneira
cujo módulo $M$ é divisível por $6$. Isso melhora a capacidade aguda de destruição
de um ataque posterior de filtro: para toda deleção posterior de um valor aceito,
remover um valor aceito pode destruir no máximo uma lacuna 2 existente.

Suponha que tanto $(x,x+2)$ quanto $(x+2,x+4)$ fossem lacunas 2 aceitas. Os três valores
$x,x+2,x+4$ ocupam todas as três classes de resíduos módulo $3$, então exatamente um é
divisível por $3$. Como $3\mid M$, esse valor não pode ser aceito. Assim,
```math
\begin{aligned}
(x,x+2)\text{ e }(x+2,x+4)\text{ ambos aceitos}
&\Longrightarrow
3\nmid x,\ 3\nmid(x+2),\ 3\nmid(x+4)
&&[\text{Aceitação}]\\
&\Longrightarrow \bot
&&[\text{Sistema Completo de Resíduos Módulo }3].
\end{aligned}
```

Equivalentemente, paridade e filtro $3$ forçam todo início de lacuna 2 a cair em um resíduo:
```math
\begin{aligned}
x,x+2\text{ accepted}
&\Longrightarrow x\equiv1\pmod2
&&[\text{Filtro }2]\\
&\Longrightarrow x\equiv5\pmod6.
&&[\text{Filtro }3;\ \text{CRT}]
\end{aligned}
```

Toda lacuna 2 destruída deve conter um valor aceito removido como extremo. Um
valor poderia pertencer a duas lacunas 2 apenas na configuração sobreposta proibida
acima. Seja $N_{\text{destroyed}}$ o número de lacunas 2 destruídas e
$N_{\text{removed}}$ o número de valores aceitos removidos.
Portanto
```math
N_{\text{destroyed}}
\le
N_{\text{removed}}.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

O isolamento limita a eficiência de destruição. Ele não implica que uma janela escolhida
contenha uma lacuna 2 antes ou depois do filtro.

O argumento de isolamento acima força $x\equiv5\pmod6$: a menor lacuna que
pode separar duas lacunas 2 consecutivas é portanto o padrão clássico de quadrupleta prima
$[2,4,2]$, uma distância de exatamente $4$, nunca menor. A figura abaixo
mede isso diretamente no mesmo conjunto de dados gerado de 200 estágios usado na
Seção 3: a distância média e máxima entre lacunas 2 consecutivas
(sequências somadas, não lacunas brutas individuais), por estágio. A média cresce de forma constante
($4\to{\sim}125$), enquanto o máximo cresce muito mais rápido (${\sim}1450$ no
último estágio), divergindo mais à medida que a cabeça cresce — mas o piso da média
fica exatamente em $4$ em todos os estágios, nunca abaixo, coincidindo com o limite de isolamento
provado acima em vez de apenas aproximá-lo.

![Distância média e máxima entre lacunas 2 consecutivas, por estágio; o piso da média é exatamente 4](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-two-cluster-size.svg)

O argumento de sobreposição acima prova sua consequência de filtragem.

<a id="43-exact-accepted-local-filter-strikes"></a>
### 4.3 Ataques Locais Aceitos Exatos por Filtro

Contar todo múltiplo de $r$ superestima a destruição local porque a maioria dos
múltiplos já foi removida por filtros menores. Para todo primo entrante
$r\ge5$ e sua próxima cabeça futura prima $Q$, os múltiplos restantes nessa
janela segura pelo quadrado admitem uma descrição exata por multiplicador primo, provada
aqui usando o postulado de Bertrand como dependência externa.

Seja
```math
M_r=\prod_{s\lt r}s,
\qquad
K=\left\lfloor\frac{Q^2-1}{r}\right\rfloor,
```

onde $s$ varia sobre primos e $Q$ é o próximo primo após $r$. Antes de
aplicar o filtro $r$, os múltiplos aceitos de $r$ em $[Q,Q^2)$ são exatamente
```math
r\ell
\qquad\text{com }\ell\text{ primo e }r\le\ell\le K.
```

Consequentemente, seu número é
```math
A(r,Q)=\pi(K)-\pi(r-1).
```

Todo múltiplo de $r$ na janela tem a forma $r\ell$ com
$2\le\ell\le K$, porque o postulado de Bertrand dá $r\lt Q\lt2r$. Como
$\gcd(r,M_r)=1$, esse valor sobreviveu aos filtros anteriores exatamente quando
$\gcd(\ell,M_r)=1$.

Bertrand's bound also gives
```math
\begin{aligned}
K
&\lt\frac{Q^2}{r}
&&[\text{Pela Definição de }K]\\
&\lt4r
&&[\text{Bertrand: }Q\lt2r]\\
&\le r^2.
&&[\text{Como }r\ge5]
\end{aligned}
```

Se um multiplicador aceito $\ell\lt K+1\le r^2$ fosse composto, seu menor divisor primo
seria no máximo $\sqrt\ell\lt r$ e dividiria $M_r$, contradizendo
$\gcd(\ell,M_r)=1$. Assim, todo multiplicador aceito é primo e pelo menos $r$.
Reciprocamente, todo primo $\ell\ge r$ é coprimo com $M_r$. Portanto
```math
\begin{aligned}
\#\{n\in[Q,Q^2):r\mid n,\ \gcd(n,M_r)=1\}
&=\#\{\ell:r\le\ell\le K,\ \ell\text{ prime}\}
&&[\text{Caracterização do Multiplicador Aceito}]\\
&=\pi(K)-\pi(r-1)
&&[\text{Definição da Contagem de Primos}]\\
&=A(r,Q).
&&\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

Esta é a contagem exata de valores aceitos atingidos pelo filtro $r$ na janela
declarada. Um valor atingido não precisa ser extremo de uma lacuna 2, então $A(r,Q)$ é apenas um
limite superior para o número de lacunas 2 locais destruídas.

A derivação acima prova a caracterização exata, incluindo sua dependência de Bertrand.

<a id="44-sharp-local-2-gap-survival-threshold"></a>
### 4.4 Limiar Local Agudo de Sobrevivência de Lacunas 2

O teorema provado é a implicação condicional abaixo; seu antecedente de abundância local
permanece aberto. Ele vale para todo primo entrante $r\ge5$, sua próxima
cabeça futura prima $Q$ e a única transição que instala o filtro $r$,
sobre inícios de lacunas 2 pré-filtro e pós-filtro cujos dois extremos permanecem
dentro de uma janela elegível e segura pelo quadrado.

A contagem exata de ataques aceitos se torna um teste determinístico agudo de sobrevivência.
Se a janela elegível contém inicialmente mais lacunas 2 do que o filtro $r$ tem
valores aceitos a remover, o isolamento dos extremos força pelo menos uma lacuna a
sobreviver.

Seja $G_{\mathrm{local}}(r,Q)$ a contagem das lacunas 2 pré-filtro $(x,x+2)$ que satisfazem
```math
Q\le x,
\qquad
x+2\lt Q^2,
```

e seja $G_{\mathrm{surviving}}(r,Q)$ a contagem daquelas ainda presentes após o filtro
$r$. Com
```math
K=\left\lfloor\frac{Q^2-1}{r}\right\rfloor,
\qquad
A(r,Q)=\pi(K)-\pi(r-1),
```

Seja $G_{\mathrm{destroyed}}(r,Q)$ a contagem das lacunas 2 elegíveis destruídas. As
propriedades de isolamento de lacunas 2 e de ataques locais aceitos dão
```math
\begin{aligned}
G_{\mathrm{destroyed}}(r,Q)
&\le\#\{\text{accepted values struck in }[Q,Q^2)\}
&&[\text{Isolamento de Lacunas 2}]\\
&=A(r,Q).
&&[\text{Ataques Locais Aceitos}]
\end{aligned}
```

Portanto,
```math
\begin{aligned}
G_{\mathrm{surviving}}(r,Q)
&=G_{\mathrm{local}}(r,Q)
  -G_{\mathrm{destroyed}}(r,Q)
&&[\text{Contabilidade da População}]\\
&\ge G_{\mathrm{local}}(r,Q)-A(r,Q).
&&[\text{Substituição}]
\end{aligned}
```

As duas contagens são inteiras, então
```math
G_{\mathrm{local}}(r,Q)>A(r,Q)
\Longrightarrow
G_{\mathrm{surviving}}(r,Q)>0.

\qquad\blacksquare\ \text{[Positividade Inteira; C.Q.D.]}
```

Equivalentemente, $A(r,Q)+1$ lacunas elegíveis pré-filtro bastam. O teorema
não prova esse antecedente de abundância local. Iterá-lo através de filtros posteriores
exigiria um novo limite de população elegível em cada transição.

A derivação acima prova o teorema condicional e sua fronteira exata.

### Notação Local de Excesso Prejudicial

Seja $Q$ uma cabeça futura prima e defina a janela elegível de inícios
```math
W_Q=\{x\in\mathbb Z:Q\le x\ \land\ x+2\lt Q^2\}.
```

Para um filtro fixo $r$, seja $K_r(I)$ a contagem dos inícios entrantes de lacunas 2 em um
intervalo $I$ destruídos porque $r$ divide um extremo. Se $N_r(I)$ é a
população entrante, defina seu excesso prejudicial centrado por
```math
b_r(I)=K_r(I)-\frac{2N_r(I)}r.
```

O termo de densidade $2N_r(I)/r$ não é, por si só, um limite superior. O sinal e o tamanho
de $b_r(I)$ codificam a informação de ordem intervalar descartada por estimativas
separadas de capacidade.

<a id="5-weighted-harmful-excess-survival"></a>

## 5. Sobrevivência por Excesso Prejudicial Ponderado

As Seções 3 e 4 contam e certificam inícios de lacunas 2; se um início certificado
sobrevive é decidido por uma quantidade sinalizada, o excesso prejudicial. Esta seção
deriva a lei exata de conservação que torna essa quantidade contabilizável
ao longo de uma cadeia condicionada inteira (5.1) e o critério terminal que transforma
sobrevivência em uma única desigualdade quadrática (5.2).

<a id="51-weighted-deletion-conservation"></a>
### 5.1 Conservação Ponderada de Deleções

A questão disparo-versus-agrupamento se torna uma lei exata de conservação sinalizada.
Cada camada tem um termo principal multiplicativo e um excesso prejudicial. Para uma
população elegível fixa de inícios de lacunas 2 acompanhada por todos os filtros em uma
cadeia condicionada completa $5\le r_0\lt r_1\lt\cdots\lt r_{m-1}\lt Q$ até uma
cabeça futura $Q$, com populações exatas por camada $N_i$, a soma ponderada
desses excessos não é uma aproximação: ela é exatamente a população final prevista
menos a população final realizada.

Seja $N_i$ o número de inícios elegíveis de lacunas 2 imediatamente antes do filtro
$r_i$, e seja $N_m$ o número que sobrevive à cadeia condicionada inteira.
Defina
```math
a_i=1-\frac2{r_i},
\qquad
A_{u,v}=\prod_{j=u}^{v-1}a_j,
\qquad
w_i=A_{i+1,m},
\qquad
w_{-1}=A_{0,m}.
```

Let
```math
T=N_0A_{0,m},
\qquad
b_i=a_iN_i-N_{i+1},
```

Além disso, $a_iw_i=A_{i,m}=w_{i-1}$ e $w_{m-1}=1$. Multiplicar a
definição de $b_i$ por $w_i$ portanto dá
```math
\begin{aligned}
\sum_{i=0}^{m-1}w_ib_i
&=\sum_{i=0}^{m-1}
  \left(w_ia_iN_i-w_iN_{i+1}\right)
&&[\text{Pela Definição de }b_i]\\
&=\sum_{i=0}^{m-1}
  \left(w_{i-1}N_i-w_iN_{i+1}\right)
&&[\text{Identidade }a_iw_i=w_{i-1}]\\
&=w_{-1}N_0-w_{m-1}N_m
&&[\text{Telescopagem}]\\
&=N_0A_{0,m}-N_m
&&[\text{Pesos de Fronteira}]\\
&=T-N_m.
&&[\text{Pela Definição de }T]
\end{aligned}
```

Isto é uma identidade, não um limite superior independente: a condição
$\sum_iw_ib_i<T$ é exatamente equivalente a $N_m>0$.

A derivação acima prova a recorrência, a identidade telescópica e a interpretação por lacuna.

<a id="52-terminal-survival-criterion"></a>
### 5.2 Critério Terminal de Sobrevivência

A desigualdade estrita de energia é suficiente para sobrevivência, para toda cadeia não vazia
$5\le r_0\lt\cdots\lt r_{m-1}\lt Q$, usando suas populações realizadas exatas,
sobre a mesma população elegível fixa de inícios de lacunas 2 e a mesma
cadeia condicionada de filtros da lei de conservação de [§5.1](#51-weighted-deletion-conservation). Provar que ela
vale para infinitas cabeças futuras permanece aberto (a estimativa terminal de sobrevivência).

Define
```math
E_b=
\sum_{i=0}^{m-1}
w_i\frac{r_i}{2(r_i-2)}b_i^2,
\qquad
W_-=\sum_{i=0}^{m-1}w_{i-1}.
```

Todo $a_i$, $w_i$ e $w_{i-1}$ é positivo, então $W_->0$.

Tome $c_i=r_i/[2(r_i-2)]$. Cauchy--Schwarz ponderado produz
```math
\begin{aligned}
(T-N_m)^2
&=\left(\sum_iw_ib_i\right)^2
&&[\text{Conservação Exata}]\\
&=\left(
  \sum_i\sqrt{w_ic_i}\,b_i
  \sqrt{\frac{w_i}{c_i}}
  \right)^2
&&[\text{Fatoração}]\\
&\le
  \left(\sum_iw_ic_ib_i^2\right)
  \left(\sum_i\frac{w_i}{c_i}\right)
&&[\text{Cauchy--Schwarz}]\\
&=E_b
  \left(\sum_i2w_i\frac{r_i-2}{r_i}\right)
&&[\text{Pela Definição de }c_i]\\
&=E_b\left(2\sum_iw_ia_i\right)
&&[\text{Substituição}]\\
&=2W_-E_b.
&&[\text{Identidade }a_iw_i=w_{i-1}]
\end{aligned}
```

Logo, a cadeia real sempre satisfaz
```math
E_b\ge\frac{(T-N_m)^2}{2W_-}.
```

Se a população final estivesse extinta, $N_m=0$, esse limite inferior se tornaria
$E_b\ge T^2/(2W_-)$. Portanto
```math
E_b\lt\frac{T^2}{2W_-}
\Longrightarrow
N_m>0.

\qquad\blacksquare\ \text{[Contradição na Extinção; C.Q.D.]}
```

A certificação de janela segura ([§4.1](#41-safe-window-2-gaps-certify-twin-primes)) então certifica o início elegível sobrevivente como um par de primos gêmeos.
A implicação é um teorema para toda cadeia condicionada completa. A estimativa terminal aberta
de sobrevivência é o enunciado aritmético de que a desigualdade estrita de energia
vale para infinitas cabeças futuras $Q$. Densidade de período completo e
limites separados de capacidade de uma camada não estabelecem essa desigualdade.

A derivação acima prova o limite inferior agudo e a classificação terminal.

<a id="6-why-the-capacity-envelope-is-exhausted"></a>
## 6. Por que o Envelope de Capacidade se Esgota

Esta seção apresenta um argumento fechado de exaustão, em vez de um único novo
teorema: ela mostra por que toda rota de capacidade sem sinal para o limiar terminal de sobrevivência
$E_b\lt T^2/(2W_-)$ falha, deixando a informação sinalizada dos resíduos como
o único ingrediente restante. Ele vale para toda cadeia condicionada não vazia
$5\le r_0\lt\cdots\lt r_{m-1}\lt Q$, sobre a mesma população elegível fixa de inícios de lacunas 2
e a mesma cadeia condicionada de filtros das propriedades acima de conservação ponderada de deleções
e critério terminal de sobrevivência. Este artigo prova os passos essenciais de exaustão
de forma autocontida no Apêndice C.

O teorema de energia terminal de [§5.2](#52-terminal-survival-criterion) reduz a sobrevivência a uma única desigualdade
sobre a energia ponderada de excesso prejudicial $E_b$. A forma mais natural de
limitar superiormente $E_b$ é maximizar separadamente a contribuição $b_i^2$ de cada camada,
usando apenas a aritmética que todo histograma de resíduos deve satisfazer. Isso produz
um *envelope de capacidade*. Os próximos seis parágrafos percorrem os resultados que
constroem, refinam e finalmente esgotam esse envelope.

<a id="61-the-separate-capacity-envelope"></a>
### 6.1 O envelope separado de capacidade

Cada classe de resíduo prejudicial pode conter no máximo $B_i$ inícios entrantes de lacunas 2, e
as duas classes prejudiciais juntas podem conter no máximo $2B_i$. O teorema agudo do
envelope de capacidade (Apêndice C.1) prova que maximizar $b_i^2$ sobre
todo histograma compatível com essas capacidades de classe dá o envelope agudo
separado por camada
```math
E_b\le\mathcal U_{\mathrm{cap}}
=\sum_i\alpha_iX_i,
\qquad
X_i=\max\bigl((\ell_i-\mu_i)^2,(u_i-\mu_i)^2\bigr),
```

com $\mu_i=2N_i/r_i$ e $\ell_i,u_i$ os extremos viáveis da contagem prejudicial.
O alargamento por estabilidade de capacidade adiciona o reparo
$\Gamma_{\mathrm{cap}}$, ampliando o limiar do certificado para
$T^2/(2W_-)+\Gamma_{\mathrm{cap}}$. O envelope de capacidade é correto e
agudo *para a informação que retém*; a pergunta é se essa informação
é suficiente.

### 6.2 Por que capacidade sozinha não dá piso positivo

O teorema do piso de largura (Apêndice C.2) prova o piso explícito por camada
```math
X_i\ge\frac14\min(N_i,2B_i,r_iB_i-N_i)^2.
```

A mesma propriedade prova a obstrução: esse piso desaparece tanto em
$N_i=0$ quanto em $N_i=r_iB_i$. Consequentemente, nenhum teorema que use apenas $r_i$ e $B_i$
pode forçar um envelope positivo, porque o perfil totalmente ocupado $N_i=r_iB_i$
é positivo e tem envelope de capacidade zero. Avançar exige ou manter
as populações realizadas longe dos dois extremos, ou substituir o intervalo de capacidade
por informação localizada de resíduos.

### 6.3 Bessel em período nativo refina, mas não conclui

O envelope híbrido de período nativo intersecta a desigualdade de Bessel sobre o
prefixo nativo com as capacidades por coordenada por meio de um programa linear guloso exato.
Isso dá o envelope híbrido
$\mathcal U_{\mathrm{hyb}}\le\mathcal U_{\mathrm{cap}}$, com ganho estrito
exatamente quando uma caixa normalizada de capacidade do prefixo excede um resto intervalar.
A quantificação de transbordamento (Apêndice C.2) mede o ganho no corte $k$ pelo
transbordamento normalizado $e_k$, que o teorema do piso de largura limita inferiormente por
folga populacional. O envelope melhora, mas as próximas três subseções mostram
que nenhum corte na cadeia consegue ultrapassar o limiar original de sobrevivência.

### 6.4 Cortes fixos falham

O teorema do corte fixo em sete (Apêndice C.3) prova que o corte fixo
imediatamente após o filtro $7$ falha: sob o piso de densidade de sete camadas na
próxima camada intocada (filtro $11$), o envelope híbrido satisfaz
```math
\mathcal U_2^{\mathrm{hyb}}>\frac{T^2}{2W_-}
\qquad\text{whenever }m\ge37.
```

O constante $37$ vem da verificação inteira exata
$29403\cdot275^2=2{,}223{,}601{,}875<37\cdot847\cdot269^2=2{,}267{,}721{,}379$.
O teorema de corte arbitrário (Apêndice C.4) generaliza isso para todo corte fixo
$k$:
```math
m>P_k(r_k-2)^2\left(1+\frac6D\right)^2
\quad\Longrightarrow\quad
\mathcal U_k^{\mathrm{hyb}}>\frac{T^2}{2W_-}.
```

Para qualquer $k$ fixo, o lado direito é limitado conforme $Q$ cresce, enquanto $m$ tende ao
infinito ao longo de qualquer família ilimitada de cabeças. Portanto, nenhum corte fixo pode
certificar sobrevivência em cadeias ilimitadas.

### 6.5 Cortes móveis perdem seus blocos nativos completos

Um corte que se move para fora com a cabeça pode, em princípio, evitar a
obstrução de corte fixo. O teorema de corte móvel (Apêndice C.5) prova a pressão
oposta: um corte que ultrapassa o limiar com pelo menos um bloco nativo completo
força
```math
m<\frac37\left(1+\frac6D\right)^2
\left(\frac{2\log H}{c}-2\right)^2,
```

onde $H$ é o comprimento da janela e $c$ é uma constante de limite inferior do tipo Chebyshev
para $\vartheta$. Esse limite é $O(\log^2 H)$. Mas o teorema dos números primos
dá $m=\pi(Q)-3\sim Q/\log Q$, então $m/\log^2H\sim Q/(4\log^3Q)\to\infty$.

O teorema dos números primos é uma dependência externa explícita aqui; a desigualdade exata
logarítmica quadrática vale sem ele sob cinco hipóteses finitas declaradas.
A conclusão assintótica exige o PNT.

Portanto, para todo $Q$ suficientemente grande, qualquer corte que ultrapasse o limiar tem
$M_k>H$: nenhum bloco nativo completo permanece. O teorema do bloco incompleto
(Apêndice C.6) então prova que o único bloco incompleto deixado nessa
escala de primo móvel contribui $e_k=0$ — a rota de capacidade nativa devolve
exatamente $\mathcal U_{\mathrm{cap}}$.

<a id="66-the-stability-gap-repair-is-negligible"></a>
### 6.6 O reparo da lacuna de estabilidade é negligível

O alargamento por estabilidade de capacidade havia aumentado o limiar do certificado por
$\Gamma_{\mathrm{cap}}$. O teorema da lacuna de estabilidade fecha essa saída: sob
o piso de densidade de sete camadas no filtro $7$,
```math
\Gamma_{\mathrm{cap}}\le\frac{25P_m}{18}\left(\frac25+\frac{3N_0}{5S}\right)^2,
\qquad
\mathcal U_{\mathrm{cap}}\ge\frac{P_mD^2}{1080}.
```

Mertens para primos e o PNT tornam a lacuna de estabilidade eventualmente positiva, mas
negligível em relação ao piso $P_mD^2/1080$. O limiar relaxado por capacidade
portanto não consegue resgatar o envelope separado de capacidade em uma
família ilimitada.

### 6.7 Veredito: informação sinalizada é necessária

O envelope capacidade-mais-Bessel-nativo não consegue certificar o limiar terminal
de sobrevivência sob o piso completo de densidade de sete camadas em cadeias ilimitadas.
Toda rota que descarta *sinais e ordem* dos resíduos — maximizando cada
camada sobre histogramas compatíveis com sinais — foi esgotada. A razão comum
é que a capacidade sem sinal esquece exatamente a informação de ordem intervalar que
controla o excesso prejudicial real.

Isso prepara as próximas duas seções. [§7](#7-exact-filter-seven-localization) calcula a primeira economia localizada genuína
no filtro $7$ ao restaurar a ordem exata dos resíduos. [§9](#9-copy-block-harmful-excess-and-residue-energy) então conecta essa
economia à energia de colisão de resíduos de [§8.2](#82-residue-collision-energy-estimate) através de blocos completos de cópias
do período antigo. As provas autocontidas completas
dos passos de exaustão resumidos em [§§6.1](#61-the-separate-capacity-envelope)--[6.6](#66-the-stability-gap-repair-is-negligible) aparecem no
Apêndice C, para que o leitor possa verificar cada constante sem sair do
artigo.

<a id="7-exact-filter-seven-localization"></a>
## 7. Localização Exata do Filtro Sete

Na primeira camada condicionada não trivial, a ordem exata dos resíduos substitui o
envelope quadrático de capacidade por uma discrepância de fronteira constante, para todo
intervalo inteiro finito $I$, depois que os filtros $2$, $3$ e $5$ foram
instalados e imediatamente antes do filtro $7$, sobre inícios reais de lacunas 2
pré-filtro 7 em um intervalo inteiro arbitrário. Este é um teorema aritmético
de localização, não uma estimativa de densidade.

Os inícios entrantes ocupam exatamente três classes módulo $30$. Defina
```math
F_7(x)=\mathbf1_{\{11,17,29\}\bmod30}(x),
\qquad
h_7(x)=\mathbf1_{\{0,5\}\bmod7}(x),
```

onde $h_7$ marca as duas classes de ataque aos extremos. O observável centrado e
sua soma intervalar são
```math
g_7(x)=F_7(x)\left(h_7(x)-\frac27\right),
\qquad
b_7(I)=\sum_{x\in I}g_7(x).
```

Como $30$ e $7$ são coprimos, $g_7$ tem período $210$. Seus 21 resíduos admissíveis
de início, em ordem crescente, são
```math
\begin{aligned}
&11,17,29,41,47,59,71,77,89,101,107,\\
&119,131,137,149,161,167,179,191,197,209.
\end{aligned}
```

Limpar o denominador dá peso $5$ em um resíduo prejudicial e $-2$ em um
resíduo inofensivo. Na ordem acima, a sequência exata é
```math
-2,-2,-2,-2,5,-2,-2,5,5,-2,-2,5,5,-2,-2,5,-2,-2,-2,-2,-2.
```

Ela contém seis termos prejudiciais e quinze inofensivos, então
```math
6\cdot5+15\cdot(-2)=0.
\qquad[\text{Cancelamento de Período Completo}]
```

Começando de zero, suas somas cumulativas são
```math
\begin{aligned}
0,&-2,-4,-6,-8,-3,-5,-7,-2,3,1,-1,\\
&4,9,7,5,10,8,6,4,2,0.
\end{aligned}
```

Seu mínimo é $-8$ e seu máximo é $10$. Toda subsoma consecutiva sem volta
é a diferença entre duas somas cumulativas. Toda subsoma com volta é o
negativo de seu complemento sem volta porque a soma completa é zero. Logo
toda subsoma cíclica $C$ satisfaz
```math
\begin{aligned}
|C|
&\le10-(-8)
&&[\text{Intervalo das Somas Cumulativas}]\\
&=18.
&&[\text{Simplificação}]
\end{aligned}
```

Agora particione qualquer intervalo inteiro $I$ em blocos completos consecutivos de
comprimento $210$ e um resto de comprimento menor que $210$. Os blocos completos
contribuem zero, e o resto seleciona uma subsoma cíclica. Portanto
```math
\begin{aligned}
|7b_7(I)|&\le18
&&[\text{Blocos Completos Cancelam}]\\
|b_7(I)|&\le\frac{18}{7}.
&&\text{[Dividir por }7\text{]}\quad\blacksquare\ \text{[C.Q.D.]}
\end{aligned}
```

O intervalo do resíduo $47$ até o resíduo $161$ atinge $18/7$, então a
constante é aguda. Para a cadeia condicionada completa com
$r_0=5$ e $r_1=7$, escreva $P_m=A_{0,m}$. Então
```math
\begin{aligned}
w_1
&=A_{2,m}
&&[\text{Pela Definição}]\\
&=\frac{P_m}{a_0a_1}
&&[\text{Fatorar }A_{0,m}]\\
&=\frac{P_m}{(3/5)(5/7)}
&&[\text{Substituir }r_0=5,\ r_1=7]\\
&=\frac{7P_m}{3},
&&[\text{Simplificação}]\\
\alpha_1
&=w_1\frac{r_1}{2(r_1-2)}
&&[\text{Coeficiente de Energia}]\\
&=\frac{49P_m}{30}.
&&[\text{Substituição}]
\end{aligned}
```

Portanto
```math
\begin{aligned}
\alpha_1b_7^2
&\le\frac{49P_m}{30}\left(\frac{18}{7}\right)^2
&&[\text{Limite Intervalar Agudo}]\\
&=\frac{54}{5}P_m.
&&[\text{Simplificação}]
\end{aligned}
```

A economia vem do padrão exato e ordenado dos resíduos. Ela controla uma
camada inicial fixa e não dá um limite uniforme para a família crescente de
coeficientes posteriores.

A derivação acima prova o certificado exato e o limite para intervalo arbitrário.

<a id="8-open-estimates-and-their-proven-reductions"></a>
## 8. Estimativas Abertas e Suas Reduções Provadas

O limite de excesso do filtro sete e as propriedades de controle de excesso por bloco de cópia são os dois últimos passos de um argumento mais longo, e a
conclusão do artigo ([§10](#10-routes-that-are-now-classified), [§12](#12-conclusion)) identifica duas estimativas abertas na fronteira ativa dos
primos gêmeos. Esta seção as introduz para que a conclusão do artigo
seja legível por si só. Ela declara a redução exata de cada estimativa,
o limite aberto e a relação com o que o artigo já provou. Reduções
algébricas adicionais (cascas de ativação, índices de elevação CRT e matrizes de Gram)
existem além do escopo do artigo. Esta seção declara as reduções exatas
necessárias para acompanhar o próprio arco do artigo e mantém a estimativa restante em aberto.

<a id="81-accepted-boundary-discrepancy-estimate"></a>
### 8.1 Estimativa de Discrepância na Fronteira Aceita

A redução abaixo é provada para toda cadeia condicionada não vazia
$5\le r_0<\cdots<r_{m-1}<Q$, sobre valores âncora aceitos em um intervalo,
acompanhados pela cadeia condicionada de filtros; a estimativa terminal
de média quadrática sinalizada permanece aberta.

Recorde de [§5.1](#51-weighted-deletion-conservation) que o excesso prejudicial na camada $i$ é
$b_i=a_iN_i-N_{i+1}$. O modelo de fronteira aceita isola o *erro de densidade de ataque*
$\varepsilon_i=H_i/A_i-1/r_i$, onde $H_i$ é a contagem de âncoras aceitas
atingidas pelo filtro $r_i$ e $A_i$ é a população de âncoras aceitas. Seu
resultado central é uma ponte exata: a densidade bruta esperada $1/r_i$ já é
exata, e o excesso prejudicial se reduz a uma diferença de somas de fronteira
de Möbius sinalizadas. Especificamente, com
$E_i=A_i-\ell\varphi(P_i)/P_i$ sendo a discrepância centrada de inclusão-exclusão
na camada $i$,
```math
H_i-\frac{A_i}{r_i}
=
\left(1-\frac1{r_i}\right)E_i-E_{i+1},
\qquad
\varepsilon_i
=
\frac{(1-1/r_i)E_i-E_{i+1}}{A_i}.
```

As discrepâncias sinalizadas telescopam sob pesos de sobrevivência de uma âncora, mas o
orçamento de energia ponderada exige uma *soma ponderada de seus quadrados*:
```math
\sum_i
w_i\frac{r_i}{2(r_i-2)}
\left(\left(1-\frac1{r_i}\right)E_i-E_{i+1}\right)^2.
```

Limitar os somandos divisores independentemente dá apenas
$|E_P|<2^{\omega(P)}-1$, exponencialmente grande demais. O sucesso exige
cancelamento sinalizado, correlação entre somas de fronteira de camadas consecutivas, ou
média entre camadas — uma entrada aritmética genuinamente nova. As propriedades desde o Núcleo de Ativação por Divisor de Ataque até a Reindexação da Primeira Deleção
catalogam as reduções por casca de ativação, elevação CRT, somatório, Gram e primeira deleção;
cada uma retorna à energia original após álgebra exata, então a
entrada restante é aritmética sinalizada, não outra reescrita de coordenadas.

**Por que este é o coeficiente geral do artigo.** O cálculo do filtro 7
de [§7](#7-exact-filter-seven-localization) é a instância de uma camada e um primo dessa mesma discrepância:
$|b_7|\le18/7$ veio da *ordem* exata dos resíduos, e o coeficiente geral de camada
$b_i$ é exatamente a discrepância de fronteira de dois resíduos estudada
aqui.

<a id="82-residue-collision-energy-estimate"></a>
### 8.2 Estimativa de Energia de Colisão de Resíduos

Para todo primo entrante $r\ge5$ e sua população real de camada condicionada,
sobre resíduos de inícios de lacunas 2 módulo um primo entrante em uma camada condicionada,
a redução abaixo é provada; a estimativa relativa de correlação de quatro pontos
permanece aberta.

A energia de colisão de resíduos é a entrada consumida pela ponte de blocos de cópia ([§9](#9-copy-block-harmful-excess-and-residue-energy)).
Seja $c_t$ a contagem dos inícios entrantes de lacunas 2 na classe de resíduo $t\bmod r$, de modo que
$N_r=\sum c_t$. O desvio centrado é $d_t=c_t-N_r/r$, e a
energia de colisão de resíduos é
```math
V_r=\sum_{t\bmod r}d_t^2.
```

As duas classes prejudiciais contêm $c_0+c_{-2}$ inícios. Seu excesso centrado
se reduz exatamente ao segundo momento do histograma e à sua autocorrelação:
```math
C_r
=
\sum_{t\bmod r}c_t^2
=
N_r+2\sum_{h\ge1}A_r(6rh),
```

onde $A_r(\cdot)$ é a autocorrelação de quatro pontos do indicador de início
no deslocamento dado. A estimativa aberta é o limite *relativo*
```math
C_r\le N_r+\frac{N_r^2}{r},
\qquad\text{equivalently}\qquad
V_r\le\frac{N_r^2}{r}.
```

Uma estimativa absoluta de peneira por limite superior é insuficiente até que sua
normalização pelo $N_r$ real seja justificada independentemente. Histogramas falsificadores
mínimos existem em pequena escala, $3+2+1$ em $(r,N)=(5,6)$;
$2+2$ em $r = 7$ e $N = 4$, mas a busca exata por camadas condicionadas até $Q\le251$
não encontrou nenhum.

**Como as duas se compõem.** A ponte de blocos de cópia de [§9](#9-copy-block-harmful-excess-and-residue-energy) prova que o
excesso prejudicial em bloco completo $B_j=d_{t_j}+d_{t_j-2}$ satisfaz
$\sum_jB_j^2\le4V_r$. Portanto, um limite relativo para a energia de colisão
de resíduos $V_r$ controla imediatamente a parte de blocos completos do excesso prejudicial
terminal. A fronteira é consequentemente uma única composição: uma estimativa relativa
de energia de resíduos alimentando a discrepância de fronteira sinalizada pela
ponte de blocos de cópia, com os dois fragmentos parciais de fronteira do período antigo ainda
abertos. Isso é exatamente o que a conclusão do artigo ([§10](#10-routes-that-are-now-classified)) nomeia.

<a id="9-copy-block-harmful-excess-and-residue-energy"></a>
## 9. Excesso Prejudicial por Bloco de Cópia e Energia de Resíduos

O excesso prejudicial de um bloco de cópia não é um escalar arbitrário. Ele é exatamente
a soma de duas entradas centradas do histograma de inícios antigos módulo $r$, para
todo período antigo $M\ge1$, todo primo entrante $r\ge5$ coprimo com $M$, toda
execução de blocos completos de cópia e todo intervalo inteiro finito no fluxo copiado,
sobre cópias elevadas de um conjunto completo de inícios de lacunas 2 do período antigo,
agrupadas em blocos de cópia do período antigo. Isso transforma energia de colisão de resíduos em
um limite quantitativo para a parte de blocos completos de um intervalo local.

Seja $S\subset[0,M)$ o conjunto de inícios antigos de lacunas 2 e tome $N=|S|$. Para
$t\bmod r$, defina
```math
c_t=\#\{a\in S:a\equiv t\pmod r\},
\qquad
d_t=c_t-\frac Nr,
\qquad
V_r=\sum_{t\bmod r}d_t^2.
```

O bloco de cópia $j$ é $[jM,(j+1)M)$. Seja $K_j$ a contagem dos inícios $a+jM$ destruídos pelo
filtro $r$ e defina seu excesso prejudicial centrado
```math
B_j=K_j-\frac{2N}{r}.
```

Defina $t_j\equiv-jM\pmod r$. Os dois ataques aos extremos são disjuntos porque
$r>2$, e são equivalentes a
```math
a\equiv t_j\pmod r,
\qquad
a\equiv t_j-2\pmod r.
```

Consequently,
```math
\begin{aligned}
K_j
&=c_{t_j}+c_{t_j-2}
&&[\text{Duas Classes de Extremos}]\\
B_j
&=d_{t_j}+d_{t_j-2}.
&&\blacksquare\ \text{[Centralização; C.Q.D.]}
\end{aligned}
```

Como $\gcd(M,r)=1$, o mapa $j\mapsto-jM\pmod r$ permuta todos os resíduos.
Além disso, $\sum_td_t=\sum_tc_t-N=0$. Logo, uma execução completa de $r$ blocos tem
```math
\begin{aligned}
\sum_{j=0}^{r-1}B_j
&=\sum_{t\bmod r}(d_t+d_{t-2})
&&[\text{Permutação de Resíduos}]\\
&=2\sum_{t\bmod r}d_t
&&[\text{Reindexação Cíclica}]\\
&=0.
&&[\text{Histograma Centrado}]
\end{aligned}
```

A mesma permutação dá a identidade exata de energia
```math
\begin{aligned}
\sum_{j=0}^{r-1}B_j^2
&=\sum_{t\bmod r}(d_t+d_{t-2})^2
&&[\text{Permutação de Resíduos}]\\
&=2V_r+2\sum_{t\bmod r}d_td_{t-2}.
&&[\text{Expansão}]
\end{aligned}
```

A autocorrelação pode ser negativa. Descartar seu sinal com
$2xy\le x^2+y^2$ dá
```math
\begin{aligned}
2\sum_td_td_{t-2}
&\le\sum_td_t^2+\sum_td_{t-2}^2
&&[\text{Limite Quadrático Termo a Termo}]\\
&=2V_r,
&&[\text{Reindexação Cíclica}]\\
\sum_{j=0}^{r-1}B_j^2
&\le4V_r.
&&\blacksquare\ \text{[Substituição; C.Q.D.]}
\end{aligned}
```

Para quaisquer $k$ blocos consecutivos com $0\le k\lt r$, Cauchy--Schwarz produz
```math
\begin{aligned}
\left|\sum_{j\in J}B_j\right|^2
&\le k\sum_{j\in J}B_j^2
&&[\text{Cauchy--Schwarz}]\\
&\le k\sum_{j=0}^{r-1}B_j^2
&&[\text{Termos Não Negativos}]\\
&\le4kV_r.
&&[\text{Energia de Blocos Completos}]
\end{aligned}
```

Assim $|\sum_{j\in J}B_j|\le2\sqrt{kV_r}$. Para uma execução mais longa, remova grupos completos
de $r$ blocos pela identidade de soma zero e tome $k$ como o número de
blocos restantes.

Um intervalo inteiro arbitrário $I$ tem um bloco parcial esquerdo do período antigo, uma sequência
de blocos completos e um bloco parcial direito. Cada bloco parcial contém no
máximo uma cópia de cada início em $S$. Como $r\ge5$ e o indicador de ataque é
ou $0$ ou $1$,
```math
\left|
\mathbf1_{r\mid x(x+2)}-\frac2r
\right|
\le1-\frac2r.
```

Cada contribuição parcial é portanto no máximo $N(1-2/r)$ em valor absoluto.
Combinar ambos os fragmentos com o limite de blocos completos dá
```math
|b_r(I)|
\le
2N\left(1-\frac2r\right)+2\sqrt{kV_r},
\qquad 0\le k\lt r.

\qquad\blacksquare\ \text{[Desigualdade Triangular; C.Q.D.]}
```

Por fim, se $C_r=\sum_tc_t^2$ é a contagem de colisões de resíduos, uma
expansão direta dá
```math
\begin{aligned}
V_r
&=\sum_t\left(c_t-\frac Nr\right)^2
&&[\text{Pela Definição}]\\
&=\sum_tc_t^2-\frac{2N}{r}\sum_tc_t+\frac{N^2}{r}
&&[\text{Expansão}]\\
&=C_r-\frac{N^2}{r}.
&&[\text{Como }\sum_tc_t=N]
\end{aligned}
```

Portanto, um teorema relativo de energia de colisão para os inícios condicionados reais
controlaria a contribuição dos blocos completos para o excesso prejudicial de [§5](#5-weighted-harmful-excess-survival).
A redução permanece incompleta: nenhum limite relativo adequado para $V_r$ é
provado ao longo das camadas crescentes, dois fragmentos parciais permanecem, e os limites por camada
ainda precisam compor sob os pesos. Quando $M$ excede toda a
janela segura pelo quadrado, pode não haver bloco completo, e o termo de fronteira
domina.

A derivação acima prova as identidades exatas, o limite de energia e a
fronteira para intervalo arbitrário.

<a id="10-routes-that-are-now-classified"></a>
## 10. Rotas que Agora Estão Classificadas

Contagens de período completo, limites de Bessel em período nativo e envelopes separados de capacidade
não resolvem o problema tardio de janela curta. A recursão por âncoras aceitas
também retorna a discrepância somatória coprima existente após cancelamento exato por CRT.
Esses fatos não refutam a condição quadrática de sobrevivência; eles identificam
qual informação adicional ela deve usar.

O programa ativo para primos gêmeos agora é estreito:
```math
\text{controlar }V_r\text{ relativamente na janela curta real,}
\quad
\text{controlar blocos parciais,}
\quad
\text{então compor as camadas sinalizadas.}
```

Mais otimização de capacidade sem sinal ou de normas de período completo não pode fornecer
esses fatos ausentes.

<a id="101-the-fixed-seed-scale-conflict"></a>
### 10.1 O Conflito de Escala com Semente Fixa

O argumento de exaustão de [§6](#6-why-the-capacity-envelope-is-exhausted) mostra que nenhum envelope de capacidade sem sinal consegue
certificar sobrevivência. Há uma razão estrutural mais profunda pela qual a
contagem de período completo não consegue posicionar um sobrevivente em uma janela escolhida: o módulo primorial
cresce além da própria janela.

Restrinja a cadeia de primos consecutivos a terminar abaixo do horizonte quadrático de seu
primo-semente $p$, de modo que a cabeça futura $Q$ satisfaça $Q<p^2$. Isso mantém
a cadeia numericamente curta, mas entra em conflito com usar muitas
cópias repetidas de um resíduo-semente fixo dentro da janela segura final $[Q,Q^2)$.
O período da semente é o primorial
```math
M_p=\prod_{r\lt p}r,
```

e pelo teorema dos números primos na forma teta de Chebyshev,
```math
\log M_p=\sum_{r\lt p}\log r\sim p.
```

Logo $M_p=\exp((1+o(1))p)$. Enquanto isso, $Q<p^2$ implica $Q^2<p^4$. Portanto
```math
\begin{aligned}
\frac{M_p}{Q^2}
&>\frac{\exp((1+o(1))p)}{p^4}
\longrightarrow\infty,
&& [\text{Limite Assintótico}]\\
M_p&>Q^2
&& [\text{Eventualmente}].
\end{aligned}
```

Para todos os cenários suficientemente grandes que satisfazem $Q<p^2$, uma classe fixa de resíduo
módulo $M_p$ ocorre no máximo uma vez em $[Q,Q^2)$. Sua frequência global exata
de repetição, portanto, não pode forçar posicionamento local.

Isso não é uma refutação da sobrevivência. Diz que uma prova não pode simultaneamente
depender de uma cadeia curta abaixo de $p^2$ e de muitas cópias locais de uma semente fixa.
Um argumento viável de média deve, em vez disso, variar sobre todos os resíduos-semente de uma vez,
usar uma semente muito anterior com uma cadeia de filtros mais longa, tirar média sobre cabeças finais
$Q$, ou introduzir uma fatoração adicional ou estrutura aditiva
que crie uma variável bilinear. O teorema dos números primos é uma dependência externa
explícita neste argumento.

Esse conflito de escala é a contraparte geométrica do veredito de exaustão:
identidades de período completo são globalmente exatas, mas se tornam localmente pouco informativas
quando o primorial excede a janela. As estimativas locais sinalizadas de [§§7](#7-exact-filter-seven-localization)--[9](#9-copy-block-harmful-excess-and-residue-energy)
são precisamente a resposta a essa obstrução.

<a id="11-a-distinct-almost-prime-program"></a>
## 11. Um Programa Distinto de Quase-Primos

Exigir que os dois extremos de uma lacuna 2 segura pelo quadrado sejam primos alcança a
fronteira dos primos gêmeos. Um programa separado relaxa o segundo extremo para ter no
máximo dois fatores primos. Esse programa tem fatores locais diferentes e uma
formulação Tipo-I/Tipo-II diferente; ele é desenvolvido separadamente.

Seu sucesso não provaria uma lacuna 2 sobrevivente nem infinitos primos gêmeos.

<a id="111-why-this-is-hard-the-type-ii-barrier"></a>
### 11.1 Por que Isso é Difícil: a Barreira Tipo-II

O argumento de exaustão e o conflito de escala com semente fixa juntos explicam
por que a álgebra de período completo deste projeto não consegue finalizar o programa de primos gêmeos.
A razão mais profunda pela qual o programa é difícil vem da
teoria contemporânea de peneiras produtoras de primos.

Ford e Maynard estudam sequências não negativas cuja diferença em relação a um
modelo de comparação satisfaz estimativas Tipo-I e Tipo-II. Tipo-I controla
médias de divisibilidade sobre muitas escalas de fatores; Tipo-II controla somas bilineares
contra sequências arbitrárias de coeficientes limitados. Seu arcabouço prova
que um *intervalo Tipo-II substancial é genuinamente necessário* para garantir um
limite inferior não trivial para primos: informação Tipo-I muito forte sozinha ainda pode
ser consistente com uma sequência sem primos.

As fórmulas exatas de resíduos e CRT deste projeto são entrada algébrica para uma
possível análise Tipo-I. Elas ainda não são um teorema Tipo-I sobre os
intervalos curtos necessários, porque a norma da discrepância acumulada ainda não
foi limitada — o conflito de escala com semente fixa de [§10.1](#101-the-fixed-seed-scale-conflict) é uma face disso.
Nenhuma estimativa Tipo-II com coeficientes arbitrários está atualmente provada para os
pesos da sequência de peneira.

O programa relaxado de quase-primos de [§11](#11-a-distinct-almost-prime-program) torna concreta a barreira Tipo-II.
Seu peso final centrado escalarmente retém um modo de caráter não principal
módulo $3$ na roda reduzida completa: um coeficiente de produto limitado pode
correlacionar perfeitamente com a contagem completa relaxada de sobreviventes. Isso refuta o
atalho segundo o qual o centramento por densidade escalar sozinho cria
ortogonalidade Tipo-II — exatamente a obstrução prevista pelo arcabouço de Ford–Maynard. A
refutação, a implicação de positividade relaxada para produção de primo-mais-$P_2$
e as propriedades exatas de divisor e caráter bilinear do programa
são provadas em [Relaxed Almost-Prime Production in Sieve
Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/relaxed-almost-prime.md).

O trabalho de Green e Sawhney sobre valores primos de $p^2+nq^2$ demonstra uma estratégia Tipo-II
moderna e bem-sucedida usando variáveis algébricas extras, fatoração em corpo de números
e maquinaria de normas de Gowers. Essas entradas estruturais não
existem automaticamente para o par afim $(x,x+2)$. Seu resultado é, portanto,
um guia metodológico, não um teorema que se transfere.

A consequência acionável é que qualquer rota além da fronteira de exaustão
de [§6](#6-why-the-capacity-envelope-is-exhausted) deve ou provar uma estimativa Tipo-I sinalizada genuína em janela curta para
as quantidades de energia de resíduos / fronteira aceita de [§8](#8-open-estimates-and-their-proven-reductions), ou introduzir uma
nova variável bilinear que forneça o cancelamento Tipo-II que falta ao par afim.

<a id="12-conclusion"></a>
## 12. Conclusão

A álgebra de peneira em período completo dá contagens globais exatas de lacunas 2 e de agrupamentos `(2,4,2)`.
Uma lacuna 2 antiga tem $r-2$ elevações sobreviventes sob um primo entrante,
cada agrupamento antigo tem $r-4$ elevações intactas, lotes finitos compõem por CRT,
rotação preserva multiplicidade cíclica, e a extinção global de lacunas 2 é estável.
Escrevendo $C_M$ para a contagem cíclica de agrupamentos no módulo $M$:
```math
\begin{aligned}
G_2(p)
&=\prod_{3\le q\lt p}(q-2),
&&[\text{Contagem Global Exata}]\\
G_{\mathrm{after}}
&=G\prod_{r\in\mathcal R}(r-2),
&&[\text{Sobrevivência Exata em Lote}]\\
C_{rM}&=(r-4)C_M,
&&[\text{Recorrência Exata de Agrupamentos}]\\
\#\{i:\text{rot}_j(G)_i=2\}
&=\#\{i:g_i=2\}.
&&[\text{Bijeção por Rotação}]\\
G_s(2)=0&\Longrightarrow G_t(2)=0\quad(t\ge s).
&&[\text{Ausência Global Estável}]
\end{aligned}
```

Os teoremas locais identificam tanto o certificado quanto a condição aguda
de uma transição:
```math
\begin{aligned}
Q\le x,\ x+2\lt Q^2,\ \gcd(x(x+2),P_Q)=1
&\Longrightarrow x,x+2\text{ prime},
&&[\text{Certificação Segura pelo Quadrado}]\\
G_{\mathrm{surviving}}(r,Q)
&\ge G_{\mathrm{local}}(r,Q)-A(r,Q),
&&[\text{Ataques Aceitos Exatos}]\\
G_{\mathrm{local}}(r,Q)>A(r,Q)
&\Longrightarrow G_{\mathrm{surviving}}(r,Q)>0.
&&[\text{Limiar Local Agudo}]
\end{aligned}
```

Para uma cadeia condicionada completa, a lei de conservação sinalizada ([§5.1](#51-weighted-deletion-conservation)) e seu
corolário ponderado de Cauchy--Schwarz ([§5.2](#52-terminal-survival-criterion)) provam
```math
\begin{aligned}
\sum_iw_ib_i&=T-N_m,
&&[\text{Conservação Exata}]\\
E_b&\ge\frac{(T-N_m)^2}{2W_-},
&&[\text{Cauchy--Schwarz Ponderado}]\\
E_b\lt\frac{T^2}{2W_-}
&\Longrightarrow N_m>0.
&&[\text{Implicação Terminal}]
\end{aligned}
```

As propriedades do Limite de Excesso do Filtro Sete até o Controle de Excesso por Bloco de Cópia então adicionam aritmética local exata:
```math
\begin{aligned}
|b_7(I)|&\le\frac{18}{7},
&&[\text{Fronteira Aguda do Filtro 7}]\\
B_j&=d_{t_j}+d_{t_j-2},
&&[\text{Fórmula Exata do Bloco de Cópia}]\\
\sum_{j=0}^{r-1}B_j^2
&=2V_r+2\sum_td_td_{t-2}
\le4V_r.
&&[\text{Ponte de Energia de Resíduos}]
\end{aligned}
```

Os resultados provados, portanto, deslocam a questão para além de densidade global e
capacidade sem sinal. Eles não completam o programa de primos gêmeos. O teorema restante
deve controlar a energia relativa de resíduos para as populações condicionadas reais,
controlar os dois fragmentos parciais de fronteira do período antigo e fazer
essas estimativas superarem o limiar terminal ponderado ao longo de uma família ilimitada
de cabeças futuras.

## Referências

1. Mata, T. H. (2026). *Formal Verification of Sieve Sequence Stages and
   Their Transitions*. Disponível em: [https://doi.org/10.5281/zenodo.22955782](https://doi.org/10.5281/zenodo.22955782).

## Apêndice A: Evidência e Estado da Verificação

A tabela separa a base verificada de construção dos novos resultados
matemáticos e da fronteira aberta. O comportamento subjacente de pertencimento
e tamanho da operação de rotação é verificado pelo Stainless, mas seu teorema exato
de multiplicidade de lacunas pertence à camada matemática.

| Grupo de afirmações | Estado | Local no artigo |
|---|---|---|
| Construção da peneira e mecânica de transição | Base verificada pelo Stainless | Artigo complementar sobre Sequências de Peneira |
| Resultados de período completo, locais, ponderados, de exaustão de capacidade, filtro sete e blocos de cópia | Provados matematicamente | [§§3--7](#3-complete-period-2-gap-properties), [§9](#9-copy-block-harmful-excess-and-residue-energy) e Apêndice C |
| Discrepância de fronteira aceita e energia de colisão de resíduos | Reduções exatas provadas; estimativas necessárias abertas | [§8](#8-open-estimates-and-their-proven-reductions) |

Entradas matemáticas externas são confinadas a dois teoremas: o postulado de Bertrand
sustenta a caracterização exata de ataques locais aceitos de
[§4.3](#43-exact-accepted-local-filter-strikes) e os corolários assintóticos
no Apêndice C, e o Teorema dos Números Primos (com estimativas de Mertens) sustenta
a discussão assintótica da lacuna de estabilidade de
[§6.6](#66-the-stability-gap-repair-is-negligible).

A construção operacional da Sequência de Peneira usada por essas propriedades
matemáticas é verificada separadamente pelo Stainless em [Formal Verification of Sieve
Sequence Stages and Their Transitions](https://doi.org/10.5281/zenodo.22955782).

## Apêndice C: Provas Autocontidas para a Cadeia de Exaustão

Este apêndice dá as provas completas dos passos de exaustão de capacidade
resumidos em [§6](#6-why-the-capacity-envelope-is-exhausted), para que o artigo seja autocontido. Cada entrada declara a
população, o escopo, a derivação e a fronteira da propriedade. Suas provas são a
autoridade para as afirmações de exaustão feitas neste artigo.

Notação compartilhada pelas entradas: $D=Q^2-Q-3$, $a_i=1-2/r_i$,
$P_i=\prod_{j<i}a_j$, $P_m=\prod_{j<m}a_j$, $T=N_0P_m$ e
$W_-=\sum_{i<m}P_m/P_i$. O envelope quadrático de excesso prejudicial por camada é
escrito como $X_i$ em todo o texto (renomeado de $M_i$ para evitar colisão com o
módulo nativo $M_k$).

### C.1 Envelope Agudo de Excesso por Capacidade Prejudicial

Fixe o histograma de resíduos de uma camada de filtro, restrito às duas classes
prejudiciais: para todo primo entrante $r>2$, toda capacidade comum de classe de resíduos
$B\ge0$ e toda população $0\le N\le rB$, sejam as contagens de resíduos $c_a$
($a\bmod r$) tais que $0\le c_a\le B$ e $\sum c_a=N$. As duas classes
prejudiciais contêm $N_{\text{harm}}=c_0+c_{-2}$ inícios, e o excesso prejudicial
sinalizado é $b=N_{\text{harm}}-2N/r$.

O total $N_{\text{harm}}$ é restringido por dois fatos. Primeiro, cada classe prejudicial
contém no máximo $B$, então $N_{\text{harm}}\le 2B$. Além disso,
$N_{\text{harm}}\le N$. Segundo, as outras $r-2$ classes contêm no máximo
$(r-2)B$ dos $N$ inícios, forçando pelo menos $N-(r-2)B$ para o par
prejudicial. O envelope de capacidade em seis partes prova que ambos os extremos são atingíveis,
dando o intervalo viável exato
```math
\ell\le N_{\text{harm}}\le u,
\qquad
\ell=\max(0,N-(r-2)B),
\qquad
u=\min(N,2B).
```

Como $b^2=(N_{\text{harm}}-2N/r)^2$ é convexo em $N_{\text{harm}}$, seu
máximo sobre $[\ell,u]$ ocorre
em um extremo:
```math
b^2
\le
X_{r,N,B}
:=
\max\left\{
\left(\ell-\frac{2N}{r}\right)^2,
\left(u-\frac{2N}{r}\right)^2
\right\}.
```

Ambos os extremos são atingíveis, então este limite é agudo. O envelope superior
da cadeia condicionada segue somando os limites agudos por camada com os coeficientes de energia
$\alpha_i=w_ir_i/[2(r_i-2)]$:
```math
E_b\le\mathcal U_{\mathrm{cap}}:=\sum_i\alpha_iX_i.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

O limite é agudo uma camada por vez, mas não precisa ser agudo
ao longo de uma cadeia, porque os histogramas que atingem cada $X_i$ separadamente podem não
coemergir de uma única sequência aninhada de sobreviventes. Uma restrição CRT entre camadas
poderia reduzir a energia agregada real abaixo de $\mathcal U_{\mathrm{cap}}$. A
propriedade não prova $\mathcal U_{\mathrm{cap}}<T^2/(2W_-)+\Gamma_{\mathrm{cap}}$;
ela reduz a rota baseada apenas em capacidade a essa desigualdade explícita.

### C.2 O Piso de Largura do Envelope de Capacidade Precisa de Folga Populacional

Para todo $r\ge5$, $B\ge0$, $0\le N\le rB$, sobre o intervalo viável
de contagem prejudicial de uma camada de filtro, esta propriedade extrai o limite inferior explícito sobre
$X_{r,N,B}$ fornecido pela
*largura* do intervalo viável $[\ell,u]$. Escreva
$c=(\ell+u)/2$, $h=(u-\ell)/2$. O extremo mais distante de $2N/r$ tem distância
```math
\max\left(\left|\frac{2N}{r}-(c-h)\right|,\left|\frac{2N}{r}-(c+h)\right|\right)
=h+\left|\frac{2N}{r}-c\right|\ge h.
```

Portanto
```math
X_{r,N,B}\ge\frac{(u-\ell)^2}{4}.
```

A largura tem a forma fechada
```math
u-\ell=\min(N,2B,rB-N).
```

Isso segue dividindo o intervalo viável em três partes. Se
$0\le N\le 2B$, então $u=N$, $\ell=0$ e $u-\ell=N$. Se
$2B\le N\le(r-2)B$, então $u=2B$, $\ell=0$ e $u-\ell=2B$. Se
$(r-2)B\le N\le rB$, então $u=2B$, $\ell=N-(r-2)B$ e $u-\ell=rB-N$. As
fórmulas coincidem nos extremos compartilhados, provando a fórmula do mínimo.
Combinando,
```math
X_{r,N,B}\ge\frac14\min(N,2B,rB-N)^2.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

**Caracterização de zero.** Como $X_{r,N,B}$ é o máximo de dois quadrados,
$X_{r,N,B}=0$ se e somente se os dois extremos forem iguais a $2N/r$, o que exige $u=\ell$. Pela
fórmula da largura, isso é equivalente a $\min(N,2B,rB-N)=0$. Como $2B>0$ e
$0\le N\le rB$, isso ocorre exatamente em
```math
X_{r,N,B}=0\iff N\in\{0,rB\}.
```

Esta é a obstrução: o envelope desaparece tanto na população vazia quanto na
população totalmente ocupada. Um teorema que usa apenas $r$ e $B$ não pode forçar um
piso positivo, porque o perfil totalmente ocupado $N=rB$ é positivo e tem
envelope de capacidade zero.

### C.3 O Corte Fixo em Sete Não Consegue Ultrapassar o Limiar Original

Considere o corte imediatamente após o filtro $7$, então $k=2$, para toda cadeia
$r_0=5,r_1=7,r_2=11,\ldots$ com $Q\ge17$ e $m\ge37$, examinando o termo de capacidade
do sufixo na primeira camada intocada (filtro $11$) de uma cadeia condicionada
e assumindo o limiar de contagem local do piso de densidade de sete camadas no
filtro $11$. O envelope híbrido de período nativo deixa toda coordenada $i\ge2$
sob seu limite separado de capacidade, dando
```math
\mathcal U_2^{\mathrm{hyb}}\ge\alpha_2X_2.
```

Os três primeiros fatores multiplicativos são $a_0=3/5$, $a_1=5/7$, $a_2=9/11$,
então $P_3=a_0a_1a_2=27/77$. Como $w_2=P_m/P_3$ e $\alpha_2=w_2/(2a_2)$,
```math
\alpha_2=\frac{P_m}{2a_2P_3}=\frac{P_m}{2\cdot(9/11)\cdot(27/77)}
=\frac{847}{486}P_m.
```

O piso de capacidade do filtro $11$ dá $X_2\ge B_{11}^2$ com
$B_{11}=\lfloor D/66\rfloor+1\ge D/66$. Portanto
```math
\mathcal U_2^{\mathrm{hyb}}\ge\frac{847}{486}P_m\left(\frac{D}{66}\right)^2.
```

Para o limite superior do limiar, $T=N_0P_m$ e $W_-=\sum_{i<m}P_m/P_i\ge mP_m$
(pois $P_i\le1$). Antes do filtro $5$, todo início de lacuna 2 é $5\bmod6$, então
$N_0\le\lfloor D/6\rfloor+1\le D/6+1$. Logo
```math
\frac{T^2}{2W_-}\le\frac{P_m}{2m}\left(\frac D6+1\right)^2.
```

O sufixo excede o limiar sempre que
```math
\frac{847}{486}\left(\frac{D}{66}\right)^2>\frac1{2m}\left(\frac D6+1\right)^2,
```

equivalentemente $m>\frac{29403}{847}(1+6/D)^2$. Para $Q\ge17$, $D\ge269$, então o
lado direito é no máximo $\frac{29403}{847}(275/269)^2$. A comparação inteira
```math
29403\cdot275^2=2{,}223{,}601{,}875<2{,}267{,}721{,}379=37\cdot847\cdot269^2
```

mostra que isso é estritamente abaixo de $37$. Portanto $m\ge37$ prova
```math
\mathcal U_2^{\mathrm{hyb}}>\frac{T^2}{2W_-}.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

Isso prova que o *envelope* não consegue certificar sobrevivência por meio desse
corte fixo. Não limita a energia real $E_b$. Não trata
cortes otimizados posteriores ($k\ge3$), o limiar relaxado por capacidade ou informação
localizada de resíduos.

### C.4 Todo Corte Nativo Fixo Falha no Limiar Original

Generalize C.3 para um corte arbitrário $k$, para toda cadeia
$5\le r_0<\cdots<r_{m-1}<Q$ com $Q\ge17$ e $2\le k<m$, sobre o termo de capacidade
do sufixo na primeira camada intocada de um corte nativo arbitrário. O
piso de densidade de sete camadas na camada $r_k$ dá
$X_k\ge B_k^2$ com $B_k=\lfloor D/(6r_k)\rfloor+1\ge D/(6r_k)$, e
$\alpha_k=P_m/(2P_ka_k^2)$. Portanto
```math
\mathcal U_k^{\mathrm{hyb}}
\ge\frac{P_mD^2}{72P_ka_k^2r_k^2}.
```

O limite superior do limiar permanece inalterado:
$T^2/(2W_-)\le(P_m/2m)(D/6+1)^2$. O sufixo excede o limiar sempre que
```math
\frac{P_mD^2}{72P_ka_k^2r_k^2}>\frac{P_m}{2m}\left(\frac D6+1\right)^2.
```

Cancelar $P_m>0$ e rearranjar dá $m>P_ka_k^2r_k^2(1+6/D)^2$. Como
$a_kr_k=r_k-2$,
```math
m>P_k(r_k-2)^2\left(1+\frac6D\right)^2
\quad\Longrightarrow\quad
\mathcal U_k^{\mathrm{hyb}}>\frac{T^2}{2W_-}.
```

Todo corte fixo eventualmente falha: para $k$ fixo, $P_k$ e $r_k$ são constantes
enquanto $(1+6/D)^2\to1$ conforme $Q$ cresce. Ao longo de qualquer família com $m\to\infty$, o
corte fixo viola a condição necessária. Assim, um corte capaz de ultrapassar o
limiar original deve se mover: $k=k(Q)\to\infty$.

Um limite inferior sem parâmetros para o primo do corte segue de $k\ge2$, dando
$P_k\le P_2=(3/5)(5/7)=3/7$. Ultrapassar o limiar exigiria
```math
m\le\frac37(r_k-2)^2\left(1+\frac6D\right)^2,
```

equivalently
```math
\mathcal U_k^{\mathrm{hyb}}<\frac{T^2}{2W_-}
\quad\Longrightarrow\quad
r_k\ge2+\frac{\sqrt{7m/3}}{1+6/D}.

\qquad\blacksquare\ \text{[C.Q.D.]}
```

**Recuperação de C.3.** Para o corte após o filtro $7$, $k=2$, $r_2=11$,
$P_2=3/7$, e $P_2(r_2-2)^2=(3/7)\cdot81=243/7=29403/847$, recuperando
exatamente a constante de C.3.

O limite $r_k\ge2+\sqrt{7m/3}/(1+6/D)$ não usa estimativa alguma para
a distribuição dos primos. É uma condição necessária sobre o primo do corte, não
suficiente: ela não prova que tal $r_k$ exista na cadeia. Converter
o limite para o primo em um limite para o índice de corte exige o teorema dos números primos
(Apêndice C.5).

### C.5 Corte Móvel Perde Blocos Nativos Completos

Para toda cadeia $5\le r_i<Q$, corte $2\le k<m$, sobre um corte nativo que se move
para fora com a cabeça futura junto com a função de contagem de primos, a
desigualdade exata logarítmica quadrática abaixo vale sob cinco hipóteses finitas
declaradas. O corolário assintótico usa o postulado de Bertrand e o teorema dos números primos
como dependências externas explícitas; o teorema exato em si é
finito, e apenas o corolário assintótico é externo.

O módulo nativo no corte $k$ é $M_k=\prod_{p<r_k}p=2\cdot3\prod_{i<k}r_i$.
Como $r_{k-1}$ é o primo imediatamente anterior a $r_k$,
```math
\log M_k=\vartheta(r_{k-1}).
```

Assuma as cinco hipóteses seguintes:

1. o piso de densidade de sete camadas vale na camada $r_k$;
2. o corte ultrapassa o limiar original, $\mathcal U_k^{\mathrm{hyb}}<T^2/(2W_-)$;
3. o módulo nativo cabe no intervalo, $M_k\le H$ onde $H=D+1=Q^2-Q-2$;
4. para alguma constante $c>0$, $\vartheta(r_{k-1})\ge cr_{k-1}$; e
5. a desigualdade de Bertrand $r_k<2r_{k-1}$.

De C.4, a hipótese 2 força
$r_k\ge2+\sqrt{7m/3}/(1+6/D)$. Das hipóteses 3--5,
```math
\log H\ge\log M_k=\vartheta(r_{k-1})\ge cr_{k-1}>\frac c2 r_k.
```

Combinando as exigências inferior e superior sobre $r_k$ e rearranjando,
```math
m<\frac37\left(1+\frac6D\right)^2\left(\frac{2\log H}{c}-2\right)^2.
```

Este é o teorema finito exato: um corte que ultrapassa o limiar com pelo menos um
bloco nativo completo força o comprimento da cadeia a ser no máximo $O(\log^2H)$.

**Corolário do teorema dos números primos (externo).** As assintóticas
$\vartheta(x)\sim x$ e $\pi(x)\sim x/\log x$ são externas à
verificação do projeto. Para a cadeia completa real, $m=\pi(Q)-3\sim Q/\log Q$, enquanto
$\log^2H\sim4\log^2Q$. Portanto
```math
\frac{m}{\log^2H}\sim\frac{Q}{4\log^3Q}\longrightarrow\infty.
```

A condição necessária exata logarítmica quadrática falha para todo $Q$ suficientemente
grande. Logo, sob o piso de densidade de sete camadas na primeira camada de sufixo,
```math
\mathcal U_k^{\mathrm{hyb}}<\frac{T^2}{2W_-}
\quad\Longrightarrow\quad
M_k>H
```

para todo $Q$ suficientemente grande e todo corte $k$. Não há blocos nativos completos
para cancelar.

Quando $M_k>H$, o envelope híbrido de período nativo ainda
restringe o único bloco intervalar incompleto. C.6 trata se essa
restrição consegue fornecer o ganho ausente. A conclusão assintótica depende
explicitamente do PNT e de Bertrand; a desigualdade exata permanece válida sem
eles sob as cinco hipóteses declaradas.

### C.6 Bessel de Bloco Incompleto Não Exclui Capacidade

Sob as hipóteses de C.4–C.5, para todo corte $2\le k<m$ com $M_k>H$, o
resto intervalar do envelope híbrido de período nativo no único bloco nativo
incompleto restante é $s_k=H$: a janela inteira é um bloco incompleto (a
escala assintótica usa Bertrand e PNT como dependências externas). Esta entrada
prova que a caixa de capacidade normalizada então cabe dentro desse orçamento, de modo que o transbordamento $e_k$
desaparece e o envelope híbrido colapsa de volta para o envelope inteiramente de capacidade.

A norma exata do envelope híbrido de período nativo na coordenada $i<k$ é
```math
q_{i,k}=\frac{M_kP_i(r_i-2)}{3r_i^2}.
```

O numerador de capacidade obedece $X_i\le N_i^2$. Como populações condicionadas
decrescem, $N_i\le N_0$, e antes do filtro $5$ todo início de lacuna 2 é $5\bmod6$,
então $N_0\le\lfloor D/6\rfloor+1\le D/5$ (usando $D\ge269>30$). Portanto
```math
X_i\le\frac{D^2}{25}.
```

Para o denominador, a função $x\mapsto(x-2)/x^2$ é decrescente para
$x\ge4$, então para $i<k$,
```math
\frac{r_i-2}{r_i^2}\ge\frac{r_k-2}{r_k^2},
\qquad
q_{i,k}\ge\frac{M_kP_k(r_k-2)}{3r_k^2}.
```

Somando as $k$ coordenadas do prefixo,
```math
\sum_{i\lt k}\frac{X_i}{q_{i,k}}
\le\frac{3kD^2r_k^2}{25M_kP_k(r_k-2)}.
```

A quantificação de transbordamento define
$e_k=(\sum_{i<k}X_i/q_{i,k}-s_k)_+$. Quando $M_k>H$, $s_k=H$. A soma normalizada
é no máximo $H$ — dando $e_k=0$ — sempre que
```math
M_kP_k\ge\frac{3kD^2r_k^2}{25H(r_k-2)}.
```

**Escala do teorema dos números primos (externa).** O produto do prefixo satisfaz
$M_kP_k=6\prod_{i<k}(r_i-2)\ge M_k/2^k$. Usando PNT e Bertrand externamente,
C.5 força $r_k\gg\sqrt{Q/\log Q}$ para qualquer corte potencialmente bem-sucedido, portanto
$\log(M_kP_k)\sim r_{k-1}\gg\sqrt{Q/\log Q}$. O logaritmo do lado direito
do critério de transbordamento zero é apenas $O(\log Q)$, pois $k<Q$,
$D<H<Q^2$ e $r_k<Q$. Portanto, o critério vale para todo $Q$ suficientemente
grande, dando
```math
e_k=0,\qquad\mathcal U_k^{\mathrm{hyb}}=\mathcal U_{\mathrm{cap}}.
```

**Exaustão do híbrido nativo original.** Combinando C.3--C.6: cortes fixos
são excluídos por C.3--C.4; qualquer corte móvel potencialmente bem-sucedido tem
$M_k>H$ (C.5) e então $\mathcal U_k^{\mathrm{hyb}}=\mathcal U_{\mathrm{cap}}$
(C.6). Como C.3 dá $\mathcal U_{\mathrm{cap}}\ge\mathcal U_2^{\mathrm{hyb}}>T^2/(2W_-)$,
o envelope capacidade-mais-Bessel-nativo satisfaz
```math
\mathcal U_{\mathrm{hyb}}\ge\frac{T^2}{2W_-}
```

para toda cadeia completa suficientemente grande que satisfaça o piso de densidade de sete camadas.
O envelope capacidade-mais-Bessel-nativo atual não consegue
certificar o limiar terminal de sobrevivência em uma família ilimitada.

Esta é uma obstrução de método, não uma refutação do
piso de densidade de sete camadas nem da estimativa terminal de sobrevivência. Ela não
trata o limiar relaxado por capacidade
$T^2/(2W_-)+\Gamma_{\mathrm{cap}}$ (tratado pelo teorema da lacuna de estabilidade,
resumido em [§6.6](#66-the-stability-gap-repair-is-negligible)) nem um limite superior localizado para o $E_b$ real.
