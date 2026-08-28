import SanguoshaNew.Rules

namespace SanguoshaNew

namespace Card

/-- 判断一张牌是否为红桃。 -/
def isHeart (c : Card) : Bool :=
  match c.suit with
  | some Suit.heart => true
  | _ => false

/-- 判断一张牌是否为黑色牌；张角发动【鬼道】时需要使用黑色牌。 -/
def isBlack (c : Card) : Bool :=
  match c.suit with
  | some suit => if suit.color = Color.black then true else false
  | none => false

/-- 判断一张牌是否为点数落在闭区间 `[lo, hi]` 内的黑桃牌。 -/
def isSpadeBetween (lo hi : Nat) (c : Card) : Bool :=
  match c.suit, c.rank with
  | some Suit.spade, some rank => lo <= rank && rank <= hi
  | _, _ => false

end Card

/-- 需要通过判定牌决定是否生效的延时锦囊。 -/
inductive DelayedTrick where
  /-- 【乐不思蜀】：最终判定牌不是红桃时生效。 -/
  | indulgence
  /-- 【闪电】：最终判定牌为黑桃 2 到黑桃 9 时生效。 -/
  | lightning
  deriving Repr, DecidableEq

namespace DelayedTrick

/-- 判断某张最终判定牌是否会让指定延时锦囊生效。 -/
def judgementTakesEffect : DelayedTrick -> Card -> Bool
  | DelayedTrick.indulgence, card => !card.isHeart
  | DelayedTrick.lightning, card => card.isSpadeBetween 2 9

end DelayedTrick

/-- 延时锦囊判定后，对游戏状态可见的结算结果。 -/
inductive JudgementOutcome where
  | noEffect
  | skipPlay
  | lightningDamage (amount : Nat)
  deriving Repr, DecidableEq

/-- 根据延时锦囊类型和最终判定牌，计算具体结算结果。 -/
def delayedTrickOutcome (trick : DelayedTrick) (card : Card) : JudgementOutcome :=
  match trick with
  | DelayedTrick.indulgence =>
      if trick.judgementTakesEffect card then
        JudgementOutcome.skipPlay
      else
        JudgementOutcome.noEffect
  | DelayedTrick.lightning =>
      if trick.judgementTakesEffect card then
        JudgementOutcome.lightningDamage 3
      else
        JudgementOutcome.noEffect

/-- 一个等待结算的判定事件：记录被判定的玩家和对应延时锦囊。 -/
structure JudgementEvent where
  target : PlayerId
  trick : DelayedTrick
  deriving Repr, DecidableEq

/--
一次判定牌改判动作。

当前模型直接记录玩家选出的替换牌。手牌移动、弃置原判定牌等区域变化可以后续继续补；
张角与司马懿的顺序争议只需要刻画“改判是否合法”和“最终判定牌是谁”。
-/
structure JudgementChange where
  actor : PlayerId
  skill : Skill
  replacement : Card
  deriving Repr, DecidableEq

/-- 判断某名玩家在当前局面下是否可以执行这次改判。 -/
def canChangeJudgement (s : GameState) (change : JudgementChange) : Bool :=
  match change.skill with
  | Skill.guicai =>
      (s.player change.actor).hasSkill Skill.guicai
  | Skill.guidao =>
      (s.player change.actor).hasSkill Skill.guidao && change.replacement.isBlack
  | _ => false

/-- 执行一次改判：被选择的替换牌成为新的当前判定牌。 -/
def applyJudgementChange (_current : Card) (change : JudgementChange) : Card :=
  change.replacement

/-- 按给定顺序处理所有改判机会，得到最终判定牌。 -/
def resolveJudgement (initial : Card) (changes : List JudgementChange) : Card :=
  changes.foldl applyJudgementChange initial

/-- 把延时锦囊的判定结果应用到当前已建模的游戏状态上。 -/
def applyJudgementOutcome
    (s : GameState) (event : JudgementEvent) (outcome : JudgementOutcome) : GameState :=
  match outcome with
  | JudgementOutcome.noEffect => s
  | JudgementOutcome.skipPlay => s
  | JudgementOutcome.lightningDamage amount =>
      let damaged := (s.player event.target).damage amount
      s.setPlayer event.target damaged

/-- 在改判顺序已经产生最终判定牌之后，结算对应的延时锦囊。 -/
def resolveDelayedTrick
    (s : GameState) (event : JudgementEvent) (finalCard : Card) : GameState :=
  applyJudgementOutcome s event (delayedTrickOutcome event.trick finalCard)

/-- 一个中性的初始牌；后续两次改判都会覆盖它。 -/
def initialJudgementCard : Card :=
  { name := CardName.basic BasicCard.slash, suit := some Suit.club, rank := some 12 }

/-- 司马懿可以发动【鬼才】，把判定牌改成这张红桃 K。 -/
def heartReplacement : Card :=
  { name := CardName.basic BasicCard.dodge, suit := some Suit.heart, rank := some 13 }

/-- 张角可以发动【鬼道】，把判定牌改成这张黑桃 2。 -/
def spadeLightningReplacement : Card :=
  { name := CardName.basic BasicCard.slash, suit := some Suit.spade, rank := some 2 }

/-- 示例改判动作：司马懿发动【鬼才】，将判定牌改成红桃 K。 -/
def simaGuicaiToHeart : JudgementChange :=
  { actor := PlayerId.b, skill := Skill.guicai, replacement := heartReplacement }

/-- 示例改判动作：张角发动【鬼道】，将判定牌改成黑桃 2。 -/
def zhangGuidaoToSpade : JudgementChange :=
  { actor := PlayerId.a, skill := Skill.guidao, replacement := spadeLightningReplacement }

/-- 用于证明改判顺序争议的局面：A 是张角，B 是司马懿。 -/
def zhangSimaOrderState : GameState :=
  { current := PlayerId.a
    phase := Phase.judge
    timing := Timing.settlement
    playerA := { general := General.zhangJiao, hp := 4, maxHp := 4 }
    playerB := { general := General.simaYi, hp := 4, maxHp := 4 } }

/-- 张角判定区里的【闪电】正在对张角本人进行判定。 -/
def lightningOnZhang : JudgementEvent :=
  { target := PlayerId.a, trick := DelayedTrick.lightning }

/-- 在示例局面中，司马懿发动【鬼才】改判是合法的。 -/
example : canChangeJudgement zhangSimaOrderState simaGuicaiToHeart = true := by
  decide

/-- 在示例局面中，张角发动【鬼道】改判是合法的。 -/
example : canChangeJudgement zhangSimaOrderState zhangGuidaoToSpade = true := by
  decide

/-- 先由司马懿改成红桃 K，再由张角改成黑桃 2 时的最终判定牌。 -/
def finalCardSimaThenZhang : Card :=
  resolveJudgement initialJudgementCard [simaGuicaiToHeart, zhangGuidaoToSpade]

/-- 先由张角改成黑桃 2，再由司马懿改成红桃 K 时的最终判定牌。 -/
def finalCardZhangThenSima : Card :=
  resolveJudgement initialJudgementCard [zhangGuidaoToSpade, simaGuicaiToHeart]

/-- 司马懿先改、张角后改时，最终判定牌确实是张角给出的黑桃 2。 -/
theorem simaThenZhang_finalCard_is_spade2 :
    finalCardSimaThenZhang = spadeLightningReplacement := by
  rfl

/-- 张角先改、司马懿后改时，最终判定牌确实是司马懿给出的红桃 K。 -/
theorem zhangThenSima_finalCard_is_heart :
    finalCardZhangThenSima = heartReplacement := by
  rfl

/-- 只交换两次改判的顺序，最终判定牌就会不同。 -/
theorem replacement_order_changes_final_card :
    finalCardSimaThenZhang != finalCardZhangThenSima := by
  decide

/-- 司马懿先改、张角后改之后，再结算【闪电】得到的局面。 -/
def stateAfterSimaThenZhang : GameState :=
  resolveDelayedTrick zhangSimaOrderState lightningOnZhang finalCardSimaThenZhang

/-- 张角先改、司马懿后改之后，再结算【闪电】得到的局面。 -/
def stateAfterZhangThenSima : GameState :=
  resolveDelayedTrick zhangSimaOrderState lightningOnZhang finalCardZhangThenSima

/-- 司马懿先改、张角后改时，最终黑桃 2 使【闪电】命中，张角受到 3 点伤害。 -/
theorem simaThenZhang_lightning_hits :
    stateAfterSimaThenZhang.playerA.hp = 1 := by
  decide

/-- 张角先改、司马懿后改时，最终红桃 K 使【闪电】不命中，张角体力不变。 -/
theorem zhangThenSima_lightning_misses :
    stateAfterZhangThenSima.playerA.hp = 4 := by
  decide

/--
争议具有实际游戏影响的形式化表述：
在同一个初始局面下，使用同样两次合法改判，只改变改判顺序，
最终得到的游戏状态不同。
-/
theorem judgement_replacement_order_affects_game_result :
    stateAfterSimaThenZhang != stateAfterZhangThenSima := by
  decide

end SanguoshaNew
