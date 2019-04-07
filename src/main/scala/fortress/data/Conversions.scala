package fortress.data

import scala.collection.JavaConverters._

object Conversions {
    def toFortressList[T](list: List[T]): fortress.data.ImmutableList[T] = 
        ImmutableWrapperList.copyCollection(list.asJava)
}
