From this preprint [\[1\]](https://figshare.com/articles/preprint/Closed_form_formulas_on_the_sums_of_three_cubes_for_k_114_192_/30509981?file=61812286), 

$\Biggl( -x + \sqrt{(6n + x)^2 + \frac{36n^3 - 19}{x}} \Biggl)^{3} + \Biggl( -x - \sqrt{(6n + x)^2 + \frac{36n^3 - 19}{x}} \Biggl)^{3} + \Biggl( 2 \cdot x + 6n \Biggl)^{3} = 114$. 

To ensure that integer solutions are yielded for this problem, 

$y^2 = (6n + x)^2 + \frac{36n^3 - 19}{x}$.

An important criterion in the above equation yielding integer solutions (and thus solving the sums of three cubes problem by extension) is this fraction $\frac{36n^3 - 19}{x} \in \mathbb{Z}$. It is highly anticipated that the solutions to the sums of three cubes problem for 114 are astronomically large in size, way beyond the capacity of modern day computing. Given that it is (obviously) unknown, values of $n,x$ for which the aforementioned fraction is an integer and by extension solves this sums of three cubes problem for integers, 
we search for large congruences of $n,x$ for which  $\frac{36n^3 - 19}{x} \in \mathbb{Z}$ with one of these two scenarios playing out: 

*When $n = p_1 k_1 + a_1$ and $x = p_2 k_2 + a_2$ , $k_1, k_2$ could be integers for which $y$ is an integer **or** $k_1, k_2$ could be non-integers for which $y$ is an integer (in which case $k_1 | p_1$ and $k_2 | p_2$).

I then posed this question to Anthropic's Claude Sonnet (Medium):

```
Can you search for the largest modular congruences you can find where for n = a_1(modp_1) and x = a_2(modp_2), a_1, a_2, p_1 ,p_2 could be as large as 30 digits to 40 digits long for all I care for which (36n^3 - 19)/x is integer? 
```
The resulting results can be found here; as .pdf ([\[2\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/large_congruences.pdf)) and as .tex ([\[3\]](https://github.com/JAgbanwa/ifykyk/blob/main/114/LargeCongruences.tex)).
