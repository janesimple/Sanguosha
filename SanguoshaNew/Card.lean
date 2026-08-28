import SanguoshaNew.Basic

namespace SanguoshaNew

/-
这个文件描述“牌面”。

注意：这里不是在创建一副完整牌堆，而是在定义 Lean 认识哪些牌名、
花色和颜色。完整牌堆需要记录每一张实体牌，后续可以再加。
-/

/-- 花色。 -/
inductive Suit where
  /-- 黑桃。 -/
  | spade
  /-- 红桃。 -/
  | heart
  /-- 梅花。 -/
  | club
  /-- 方块。 -/
  | diamond
  deriving Repr, DecidableEq

/-- 颜色。黑桃/梅花是黑色，红桃/方块是红色。 -/
inductive Color where
  | black
  | red
  deriving Repr, DecidableEq

/-- 由花色得到颜色。 -/
def Suit.color : Suit -> Color
  | Suit.spade => Color.black
  | Suit.club => Color.black
  | Suit.heart => Color.red
  | Suit.diamond => Color.red

/--
基础牌。

这里把普通【杀】、【火杀】、【雷杀】分开列出，但在很多规则判断里
它们都会被当成“杀类牌”。
-/
inductive BasicCard where
  | slash
  | fireSlash
  | thunderSlash
  | dodge
  | peach
  | wine
  deriving Repr, DecidableEq

/-- 判断一张基础牌是否属于“杀类牌”。 -/
def BasicCard.isSlash : BasicCard -> Bool
  | BasicCard.slash => true
  | BasicCard.fireSlash => true
  | BasicCard.thunderSlash => true
  | _ => false

/-- 当前模型中已经需要精确区分的锦囊牌。 -/
inductive TacticCard where
  /-- 【顺手牵羊】：从目标处获得一张牌。 -/
  | snatch
  /-- 【借刀杀人】：令一名角色对另一名角色使用【杀】。 -/
  | borrowedSword
  /-- 其他暂未展开效果的锦囊。 -/
  | other
  deriving Repr, DecidableEq

/-- 当前模型中已经需要精确区分的武器牌。 -/
inductive WeaponCard where
  /-- 【丈八蛇矛】：可以将两张手牌当一张【杀】使用。 -/
  | zhangbaSnakeSpear
  /-- 其他暂未展开效果的武器。 -/
  | other
  deriving Repr, DecidableEq

/--
牌名的大分类。

第一版只详细区分基础牌。锦囊牌和装备牌先只保留大类，
这样状态模型可以预留扩展位置，但规则暂时不会被复杂牌拖住。
-/
inductive CardName where
  | basic (card : BasicCard)
  | tactic
  | equipment
  deriving Repr, DecidableEq

/--
一张“牌面”。

`Option Suit` 表示花色可以有，也可以没有：
* `some Suit.spade` 表示已知是黑桃；
* `none` 表示当前模型不关心或暂时不知道花色。

`rank` 同理，后续如果要实现判定牌点数、丈八蛇矛等细节，可以继续用它。
当前框架主要按牌名计数，所以还不区分同名牌的实体副本。
-/
structure Card where
  name : CardName
  suit : Option Suit := none
  rank : Option Nat := none
  deriving Repr, DecidableEq

namespace CardName

/-- 常用缩写：普通【杀】。 -/
def slash : CardName := CardName.basic BasicCard.slash
/-- 常用缩写：【闪】。 -/
def dodge : CardName := CardName.basic BasicCard.dodge
/-- 常用缩写：【桃】。 -/
def peach : CardName := CardName.basic BasicCard.peach
/-- 常用缩写：【酒】。 -/
def wine : CardName := CardName.basic BasicCard.wine
/-- 常用缩写：锦囊牌大类。 -/
def tacticAny : CardName := CardName.tactic
/-- 常用缩写：装备牌大类。 -/
def equipmentAny : CardName := CardName.equipment

/-- 判断一个牌名是否属于“杀类牌”。 -/
def isSlash : CardName -> Bool
  | CardName.basic c => c.isSlash
  | _ => false

end CardName

end SanguoshaNew
