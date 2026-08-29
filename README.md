# SanguoshaNew

这是一个独立的 Lean 4 工程，用来把三国杀的基础规则写成可以被
Lean 检查的形式化模型。

规则参考来源：<https://gltjk.com/sanguosha/rules/>

## 本轮更新

这次主要是把项目往“学员可读、可练、可验证”的方向再推一步：

- 新增 `SanguoshaNew/Exercises.lean`，把 `legal`、`transition`、`healOne`、自然数不等式等基础证明拆成练习题。
- 扩充 `SanguoshaNew/Examples.lean`，补进非法命令返回 `none`、以及 `endPhase` 这类可直接运行的样例。
- 在 `SanguoshaNew/Rules.lean` 里补了两个关键桥梁引理：`transition_eq_none_iff_not_legal` 和 `legal_of_transition_some`。
- 在 `SanguoshaNew/State.lean` 里补齐了牌池总数、玩家牌数守恒等基础引理，方便后续 `simp` 证明。
- 新增 `STUDY_GUIDE.md`，把阅读顺序和练习路径单独列出来，避免把正式证明和训练材料混在一起。

## 给初学者的阅读方式

不要一上来就看证明。建议按这个顺序：

1. `SanguoshaNew/Basic.lean`
   先认识最基础的枚举：阶段、时机、区域、玩家。

2. `SanguoshaNew/Card.lean`
   看牌名、花色、颜色是怎么表示的。

3. `SanguoshaNew/State.lean`
   看一个“局面”在 Lean 里长什么样。

4. `SanguoshaNew/Rules.lean`
   看什么叫合法行动，以及行动如何改变局面。

5. `SanguoshaNew/Judgement.lean`
   看判定牌、延时锦囊、张角【鬼道】、司马懿【鬼才】和改判顺序证明。

6. `SanguoshaNew/MaLiangSixDamage.lean`
   看马良、郝昭、神郭嘉场景下的六伤路径，以及“任意未知牌 X 都成立”的证明。

7. `SanguoshaNew/Examples.lean`
   看几个具体例子，例如 A 对 B 出杀、B 出闪、A 吃桃。

8. `SanguoshaNew/Exercises.lean`
   先做一组短练习，把 `decide`、`simp`、`omega` 和基础引理串起来。

9. `SanguoshaNew/Invariant.lean`
   最后看证明，例如“使用一张牌只是移动牌的位置，总牌数不变”。

## 当前建模范围

第一版只做基础框架：

- 两名玩家；
- 当前回合玩家；
- 回合阶段和时机；
- 手牌、装备区、判定区、摸牌堆、弃牌堆、处理区；
- 基础牌：【杀】、【火杀】、【雷杀】、【闪】、【桃】、【酒】；
- 使用【杀】后的响应窗口；
- 【闪】响应【杀】；
- 【桃】回复体力；
- 【酒】强化下一张【杀】或濒死自救；
- 武将：张角、司马懿、马良、郝昭、神郭嘉和普通武将；
- 技能：【鬼道】、【鬼才】、【自书】、【应援】、【镇骨】、【慧识】、【天翊】、【辉逝】；
- 判定牌的花色、颜色和点数判断；
- 延时锦囊：【乐不思蜀】、【闪电】；
- 判定牌改判动作和按顺序结算；
- 张角与司马懿同时可改判时，不同改判顺序会改变最终游戏结果的证明；
- 锦囊/武器名登记：【顺手牵羊】、【借刀杀人】、【丈八蛇矛】；
- 马良装备【丈八蛇矛】时，配合【酒】【应援】【自书】形成六伤路径的证明；
- 六伤路径中【自书】摸到的未知牌用变量 `X` 表示，并对所有可能牌类做全称证明；
- 非法行动返回 `none`；
- 合法行动返回 `some 新局面`。

## 还没有实现的内容

这些不是忘了，而是故意先不放进第一版：

- 距离和攻击范围；
- 武器、防具、坐骑的具体效果；
- 其他武将技能，以及已登记技能的完整通用结算；
- 身份、胜利条件；
- 完整牌堆顺序；
- 多目标锦囊；
- 判定牌从牌堆翻出、原判定牌和替换牌进入弃牌堆的完整区域移动；
- 延时锦囊在判定区内的放置、转移和弃置流程；
- 【借刀杀人】的完整合法性检查，例如目标装备区武器条件、距离和响应窗口；
- 【丈八蛇矛】虚拟牌使用后的完整区域移动；
- 多人局通用 `GameState`；马良六伤证明目前使用专门的三方最小状态；
- 濒死求桃的完整流程。

## 张角与司马懿改判顺序证明

新增的 `SanguoshaNew/Judgement.lean` 用一个最小局面刻画经典争议：

- A 是张角，拥有【鬼道】；
- B 是司马懿，拥有【鬼才】；
- 张角正在进行【闪电】判定；
- 司马懿选择把判定牌改成红桃 K；
- 张角选择把判定牌改成黑桃 2。

模型中，改判按列表顺序依次覆盖当前判定牌：

```lean
resolveJudgement initialJudgementCard [simaGuicaiToHeart, zhangGuidaoToSpade]
resolveJudgement initialJudgementCard [zhangGuidaoToSpade, simaGuicaiToHeart]
```

因此：

- 司马懿先改、张角后改：最终判定牌是黑桃 2，【闪电】命中，张角体力从 4 变成 1；
- 张角先改、司马懿后改：最终判定牌是红桃 K，【闪电】不命中，张角体力仍为 4。

对应的核心定理是：

```lean
judgement_replacement_order_affects_game_result
```

它说明：在同一个初始局面下，使用同样两次合法改判，只改变改判顺序，最终游戏状态就会不同。

## 马良六伤路径证明

`SanguoshaNew/MaLiangSixDamage.lean` 形式化了下面这个三方局面：

- 马良装备【丈八蛇矛】；
- 马良手牌为【酒】、两张【杀】、【顺手牵羊】、【借刀杀人】；
- 马良拥有锁定技【自书】和主动技【应援】；
- 场上有队友郝昭；
- 对手神郭嘉体力为 5，手牌为 0，且没有会干预本路径伤害的防御技能。

行动序列是：

1. 马良使用【酒】，令本回合下一张【杀】伤害 +1。
2. 马良发动【丈八蛇矛】，将两张【杀】当一张【杀】使用；配合【酒】造成 2 点伤害，并通过【应援】把这两张【杀】交给郝昭。
3. 马良使用【借刀杀人】，令郝昭对神郭嘉出【杀】；按题设路径造成 2 点伤害，并通过【应援】把【借刀杀人】交给神郭嘉。
4. 马良使用【顺手牵羊】，从神郭嘉手牌中拿回【借刀杀人】；因【自书】锁定触发，额外摸到一张未知牌 `X`。
5. 马良再次使用【借刀杀人】，令郝昭再次对神郭嘉出【杀】，造成最后 2 点伤害。

这里的关键不是 `X` 的牌质，而是数量不变量：

```lean
after_step_four_has_borrowed_sword_for_any_drawn
```

该定理说明：第四步之后，无论【自书】摸到的 `X` 是什么，马良都至少持有一张【借刀杀人】。

最终结论写成：

```lean
maliang_has_six_damage_path_for_any_unknown_card
```

它的含义是：

```lean
∀ drawn : SixDamageCard,
  ∃ actions : List SixDamageAction,
    actions = sixDamageActions drawn ∧
      (runSixDamagePath drawn).totalDamageToShen >= 6 ∧
      (runSixDamagePath drawn).shenGuojiaHp = 0
```

也就是说，对任意未知牌 `drawn`，都存在同一条五步行动序列，
总伤害大于等于 6，并且五血神郭嘉最终体力归零。

## 几个 Lean 关键词

- `inductive`：列举一种东西有哪些可能情况，例如阶段只有六种。
- `structure`：把多个字段打包成一个对象，例如一个玩家有体力和手牌。
- `def`：定义函数或值。
- `Prop`：命题，例如“这个玩家手里有杀”。
- `Bool`：布尔值，只有 `true` 和 `false`。
- `Option GameState`：可能有新局面，也可能没有。
- `some s`：成功得到新局面 `s`。
- `none`：失败，通常表示行动不合法。
- `theorem`：Lean 检查过的数学断言。
- `example`：没有名字的小定理，适合写测试样例。
- `by decide`：让 Lean 自动判断一个简单命题。
- `omega`：Lean 的自然数/整数线性算术证明工具。

## 构建

```powershell
$env:ELAN_HOME = "C:\Users\15036\.elan"
lake build
lake exe sanguosha-new
```

## 文件结构

```text
SanguoshaNew/
  Basic.lean      基础名词：阶段、时机、区域、玩家
  Card.lean       牌面：花色、颜色、基础牌、牌名
  State.lean      局面：牌池、玩家状态、整体游戏状态
  Rules.lean      规则：合法性判断和状态转移
  Judgement.lean  判定：延时锦囊、改判技能、改判顺序证明
  MaLiangSixDamage.lean
                  路径：马良、郝昭、神郭嘉场景下的六伤证明
  Exercises.lean  练习：基础证明和 `transition` 相关练习
  Invariant.lean  证明：牌数守恒等性质
  Examples.lean   样例：能直接跑通的小局面
  STUDY_GUIDE.md   学习路线：先读什么、先练什么
```

## 当前核心思想

本工程最重要的设计是：

```lean
transition : GameState -> Command -> Option GameState
```

意思是：

给定一个局面 `GameState` 和一个玩家命令 `Command`，
Lean 会尝试计算下一个局面。

如果命令合法，返回：

```lean
some 新局面
```

如果命令非法，返回：

```lean
none
```

这样做的好处是，非法操作不会被悄悄当成正常操作处理。

判定系统的核心设计是：

```lean
resolveJudgement : Card -> List JudgementChange -> Card
```

意思是：

给定一张初始牌和一串改判动作，Lean 按顺序依次应用这些改判，
最后得到唯一的最终判定牌。张角与司马懿争议的关键就在于：
同样的两次改判，如果顺序不同，最后覆盖当前判定牌的人也不同。

马良六伤路径的核心设计是：

```lean
runSixDamagePath : SixDamageCard -> SixDamageState
```

意思是：

把【自书】摸到的未知牌作为参数传入，然后执行固定五步路径。
最终定理对这个参数做全称量化，所以证明结果不依赖摸到哪张牌。
