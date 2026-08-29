import SanguoshaNew.Basic
import SanguoshaNew.Card
import SanguoshaNew.State
import SanguoshaNew.Rules
import SanguoshaNew.Judgement
import SanguoshaNew.MaLiangSixDamage
import SanguoshaNew.Invariant
import SanguoshaNew.Examples
import SanguoshaNew.Exercises

/-!
这是整个工程的总入口文件。

在 Lean 里，一个工程通常会有一个和库同名的 `.lean` 文件，用来集中
`import` 下面的子模块。这样其他文件只要写 `import SanguoshaNew`，
就可以一次性拿到本工程暴露出来的主要定义。

本工程先做“三国杀规则的最小形式化框架”，不追求一次性实现完整游戏。
当前覆盖的核心概念是：

* 回合阶段：准备、判定、摸牌、出牌、弃牌、结束；
* 牌所在的区域：手牌、装备区、判定区、牌堆、弃牌堆、处理区；
* 基本牌：杀、火杀、雷杀、闪、桃、酒；
* 行动是否合法；
* 杀产生的响应窗口；
* 合法行动带来的状态变化；
* 判定牌、延时锦囊和改判顺序；
* 马良、郝昭、神郭嘉场景下的六伤路径；
* 一些最小证明，例如“牌从手牌移动到弃牌堆时，总牌数不变”。

阅读建议：

1. 先看 `Basic.lean` 和 `Card.lean`，它们只是“名词表”。
2. 再看 `State.lean`，理解我们怎样描述一个局面。
3. 然后看 `Rules.lean`，理解合法性和结算。
4. 再看 `Judgement.lean` 与 `MaLiangSixDamage.lean`，理解两个具体争议的形式化证明。
5. 最后看 `Examples.lean` 与 `Invariant.lean`。
-/
