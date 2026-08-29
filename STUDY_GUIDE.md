# 学员版阅读路线

这份项目更适合按“课程练习”来读，而不是按完整游戏引擎来读。

## 建议顺序

1. `SanguoshaNew/Basic.lean`
   先看 `inductive`、`structure`、`def` 这些最基础的定义。
2. `SanguoshaNew/Card.lean`
   了解牌名、花色、点数是怎么编码的。
3. `SanguoshaNew/State.lean`
   了解局面是怎么拆成牌池、玩家、阶段、时机的。
4. `SanguoshaNew/Rules.lean`
   看 `legal` 和 `transition` 的分工。
5. `SanguoshaNew/Exercises.lean`
   先做这些小练习，熟悉 `cases`、`simp`、`decide`、`omega`。
6. `SanguoshaNew/Judgement.lean`
   看改判顺序如何影响最终结果。
7. `SanguoshaNew/MaLiangSixDamage.lean`
   看如何把一条固定路径拆成可证明的步骤。
8. `SanguoshaNew/Invariant.lean`
   看局部引理如何拼成总不变量。

## 这次改良的重点

- 把练习和正式证明分开。
- 给同一个结论保留不同证明风格。
- 让每个大证明都能追溯到更小的局部引理。
- 给规则层加清晰的中文说明，方便回看。

