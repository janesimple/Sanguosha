import SanguoshaNew.State

namespace SanguoshaNew

/-
这个文件专门形式化马良、郝昭、神郭嘉场景下的“六伤路径”。

当前主规则引擎 `GameState` 仍是两人局骨架，而这个例子天然涉及三名角色。
为了不提前重写整个多人局引擎，这里建立一个只服务于该证明的小状态：
它只记录这条路径需要关心的手牌数量、马良的装备/技能标记、神郭嘉体力和累计伤害。
-/

/-- 六伤路径证明中需要区分的手牌类型。 -/
inductive SixDamageCard where
  /-- 【酒】。 -/
  | wine
  /-- 【杀】。 -/
  | slash
  /-- 【顺手牵羊】。 -/
  | snatch
  /-- 【借刀杀人】。 -/
  | borrowedSword
  /-- 任意其他牌；也用于承载【自书】摸到的未知牌。 -/
  | other
  deriving Repr, DecidableEq

/-- 六伤路径中展示给读者看的行动标签。 -/
inductive SixDamageAction where
  /-- 第一步：马良使用【酒】。 -/
  | useWine
  /-- 第二步：马良发动【丈八蛇矛】，将两张【杀】当一张【杀】使用。 -/
  | zhangbaSlashWithTwoSlash
  /-- 第三步：马良使用第一张【借刀杀人】，令郝昭对神郭嘉出【杀】。 -/
  | firstBorrowedSword
  /-- 第四步：马良使用【顺手牵羊】拿回【借刀杀人】，并因【自书】摸到未知牌。 -/
  | snatchBackBorrowedSwordAndZishu (drawn : SixDamageCard)
  /-- 第五步：马良再次使用【借刀杀人】，令郝昭再次对神郭嘉出【杀】。 -/
  | secondBorrowedSword
  deriving Repr, DecidableEq

/-- 只按牌名计数的手牌结构。 -/
structure SixDamageHand where
  wine : Nat := 0
  slash : Nat := 0
  snatch : Nat := 0
  borrowedSword : Nat := 0
  other : Nat := 0
  deriving Repr, DecidableEq

namespace SixDamageHand

/-- 空手牌。 -/
def empty : SixDamageHand := {}

/-- 获得一张指定类型的牌。 -/
def inc (h : SixDamageHand) : SixDamageCard -> SixDamageHand
  | SixDamageCard.wine => { h with wine := h.wine + 1 }
  | SixDamageCard.slash => { h with slash := h.slash + 1 }
  | SixDamageCard.snatch => { h with snatch := h.snatch + 1 }
  | SixDamageCard.borrowedSword => { h with borrowedSword := h.borrowedSword + 1 }
  | SixDamageCard.other => { h with other := h.other + 1 }

/-- 失去一张指定类型的牌；调用者负责保证该牌原本存在。 -/
def dec (h : SixDamageHand) : SixDamageCard -> SixDamageHand
  | SixDamageCard.wine => { h with wine := h.wine - 1 }
  | SixDamageCard.slash => { h with slash := h.slash - 1 }
  | SixDamageCard.snatch => { h with snatch := h.snatch - 1 }
  | SixDamageCard.borrowedSword => { h with borrowedSword := h.borrowedSword - 1 }
  | SixDamageCard.other => { h with other := h.other - 1 }

/-- 手牌总数；用于表达【自书】带来的数量保证。 -/
def total (h : SixDamageHand) : Nat :=
  h.wine + h.slash + h.snatch + h.borrowedSword + h.other

end SixDamageHand

/-- 马良六伤路径所需的三方最小状态。 -/
structure SixDamageState where
  /-- 马良的手牌。 -/
  maLiangHand : SixDamageHand
  /-- 郝昭的手牌。 -/
  haoZhaoHand : SixDamageHand
  /-- 神郭嘉的手牌。 -/
  shenGuojiaHand : SixDamageHand
  /-- 马良是否装备【丈八蛇矛】。 -/
  maLiangHasZhangba : Bool
  /-- 马良是否拥有锁定技【自书】。 -/
  maLiangHasZishu : Bool
  /-- 马良是否拥有主动技【应援】。 -/
  maLiangHasYingyuan : Bool
  /-- 神郭嘉是否有会干预本路径伤害的防御技能；题设为没有。 -/
  shenGuojiaHasDefense : Bool
  /-- 神郭嘉当前体力。 -/
  shenGuojiaHp : Nat
  /-- 本路径已经对神郭嘉造成的累计伤害。 -/
  totalDamageToShen : Nat := 0
  /-- 【酒】提供给本回合下一张【杀】的伤害加值。 -/
  wineBuff : Nat := 0
  deriving Repr, DecidableEq

/-- 初始局面：马良五张手牌，装备【丈八蛇矛】，队友郝昭在场，神郭嘉五血零手牌且无防御干预。 -/
def sixDamageInitialState : SixDamageState :=
  { maLiangHand :=
      { SixDamageHand.empty with
        wine := 1
        slash := 2
        snatch := 1
        borrowedSword := 1 }
    haoZhaoHand := SixDamageHand.empty
    shenGuojiaHand := SixDamageHand.empty
    maLiangHasZhangba := true
    maLiangHasZishu := true
    maLiangHasYingyuan := true
    shenGuojiaHasDefense := false
    shenGuojiaHp := 5 }

/-- 对神郭嘉造成伤害，同时记录累计伤害。自然数减法会把体力下限截断为 0。 -/
def damageShenGuojia (amount : Nat) (s : SixDamageState) : SixDamageState :=
  { s with
    shenGuojiaHp := s.shenGuojiaHp - amount
    totalDamageToShen := s.totalDamageToShen + amount }

/-- 第一步：马良使用【酒】，得到“下一张【杀】伤害 +1”的标记。 -/
def stepUseWine (s : SixDamageState) : SixDamageState :=
  { s with
    maLiangHand := s.maLiangHand.dec SixDamageCard.wine
    wineBuff := 1 }

/--
第二步：马良发动【丈八蛇矛】，将两张【杀】当一张【杀】使用。

这张虚拟【杀】受到【酒】加成，造成 `1 + wineBuff = 2` 点伤害。
随后马良发动【应援】，把作为虚拟【杀】素材的两张【杀】交给队友郝昭。
-/
def stepZhangbaSlashAndYingyuan (s : SixDamageState) : SixDamageState :=
  let damage := 1 + s.wineBuff
  { damageShenGuojia damage s with
    maLiangHand := (s.maLiangHand.dec SixDamageCard.slash).dec SixDamageCard.slash
    haoZhaoHand := (s.haoZhaoHand.inc SixDamageCard.slash).inc SixDamageCard.slash
    wineBuff := 0 }

/--
第三步：马良使用【借刀杀人】，令郝昭对神郭嘉出【杀】。

本证明按题设文字抽象该次【杀】造成 2 点伤害；随后马良发动【应援】，
把结算后的【借刀杀人】交给神郭嘉。
-/
def stepFirstBorrowedSwordAndYingyuan (s : SixDamageState) : SixDamageState :=
  let afterDamage := damageShenGuojia 2 s
  { afterDamage with
    maLiangHand := s.maLiangHand.dec SixDamageCard.borrowedSword
    haoZhaoHand := s.haoZhaoHand.dec SixDamageCard.slash
    shenGuojiaHand := s.shenGuojiaHand.inc SixDamageCard.borrowedSword }

/--
第四步：马良使用【顺手牵羊】，从神郭嘉手牌中拿回【借刀杀人】。

由于这是马良回合内获得的非【自书】牌，【自书】作为锁定技强制触发，
马良额外摸一张未知牌 `drawn`。证明不会假设这张牌是什么。
-/
def stepSnatchBackAndZishuDraw (drawn : SixDamageCard) (s : SixDamageState) : SixDamageState :=
  { s with
    maLiangHand := ((s.maLiangHand.dec SixDamageCard.snatch).inc SixDamageCard.borrowedSword).inc drawn
    shenGuojiaHand := s.shenGuojiaHand.dec SixDamageCard.borrowedSword }

/-- 第五步：马良再次使用【借刀杀人】，郝昭再次出【杀】，对神郭嘉造成 2 点伤害。 -/
def stepSecondBorrowedSword (s : SixDamageState) : SixDamageState :=
  damageShenGuojia 2
    { s with
      maLiangHand := s.maLiangHand.dec SixDamageCard.borrowedSword
      haoZhaoHand := s.haoZhaoHand.dec SixDamageCard.slash }

/-- 题设中的五步行动序列，其中第四步记录【自书】摸到的未知牌。 -/
def sixDamageActions (drawn : SixDamageCard) : List SixDamageAction :=
  [ SixDamageAction.useWine,
    SixDamageAction.zhangbaSlashWithTwoSlash,
    SixDamageAction.firstBorrowedSword,
    SixDamageAction.snatchBackBorrowedSwordAndZishu drawn,
    SixDamageAction.secondBorrowedSword ]

/-- 执行完整六伤路径。 -/
def runSixDamagePath (drawn : SixDamageCard) : SixDamageState :=
  stepSecondBorrowedSword
    (stepSnatchBackAndZishuDraw drawn
      (stepFirstBorrowedSwordAndYingyuan
        (stepZhangbaSlashAndYingyuan
          (stepUseWine sixDamageInitialState))))

/-- 执行到第四步之后的状态；用于单独表达【自书】给出的数量保证。 -/
def stateAfterStepFour (drawn : SixDamageCard) : SixDamageState :=
  stepSnatchBackAndZishuDraw drawn
    (stepFirstBorrowedSwordAndYingyuan
      (stepZhangbaSlashAndYingyuan
        (stepUseWine sixDamageInitialState)))

/-- 马良的技能包中确实登记了【自书】。 -/
example : General.maLiang.hasSkill Skill.zishu = true := by
  decide

/-- 马良的技能包中确实登记了【应援】。 -/
example : General.maLiang.hasSkill Skill.yingyuan = true := by
  decide

/-- 郝昭的技能包已登记；本证明不需要展开【镇骨】效果。 -/
example : General.haoZhao.hasSkill Skill.zhengu = true := by
  decide

/-- 神郭嘉的技能包已登记；题设同时假定这些技能不形成防御干预。 -/
example : General.shenGuojia.hasSkill Skill.shenHuishi = true := by
  decide

/--
第四步之后，马良一定至少持有一张【借刀杀人】。

这正是【自书】提供的数量不变量在本路径中的作用：
未知牌 `drawn` 可以是任意牌；即使它不是【借刀杀人】，
马良也已经通过【顺手牵羊】拿回了第一张【借刀杀人】。
-/
theorem after_step_four_has_borrowed_sword_for_any_drawn
    (drawn : SixDamageCard) :
    (stateAfterStepFour drawn).maLiangHand.borrowedSword >= 1 := by
  cases drawn <;> decide

/--
对任意未知牌 `drawn`，完整路径对神郭嘉造成的累计伤害都等于 6。

证明对 `drawn` 做全称量化，覆盖【自书】可能摸到的所有牌类；
数值部分由 `omega` 处理，和未知牌无关的化简由 `simp` 展开。
-/
theorem run_six_damage_path_total_damage_eq_six_for_any_drawn
    (drawn : SixDamageCard) :
    (runSixDamagePath drawn).totalDamageToShen = 6 := by
  cases drawn <;> decide

/--
形式化结论：无论【自书】摸到的未知牌是什么，都存在题设五步行动序列，
使得总伤害大于等于 6，并且五血神郭嘉最终体力归零。
-/
theorem maliang_has_six_damage_path_for_any_unknown_card :
    ∀ drawn : SixDamageCard,
      ∃ actions : List SixDamageAction,
        actions = sixDamageActions drawn ∧
          (runSixDamagePath drawn).totalDamageToShen >= 6 ∧
          (runSixDamagePath drawn).shenGuojiaHp = 0 := by
  intro drawn
  exists sixDamageActions drawn
  constructor
  · rfl
  · constructor
    · have hdamage := run_six_damage_path_total_damage_eq_six_for_any_drawn drawn
      omega
    · cases drawn <;> decide

end SanguoshaNew

/-- 同一个结论的分析式写法：先得到等式，再交给 `omega`。 -/
theorem SanguoshaNew.run_six_damage_path_total_damage_ge_six
    (drawn : SanguoshaNew.SixDamageCard) :
    (SanguoshaNew.runSixDamagePath drawn).totalDamageToShen >= 6 := by
  have h : (SanguoshaNew.runSixDamagePath drawn).totalDamageToShen = 6 := by
    cases drawn <;> decide
  omega
