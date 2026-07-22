import v1.chapter3.list.ListBuilder.createList
import v1.chapter3.list.ListUtils

val list = createList(Array(BigInt(1),BigInt(2),BigInt(3)))

ListUtils.sum(list)

ListUtils.slice(list, 0, 2)