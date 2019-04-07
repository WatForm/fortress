package fortress.data

import scala.collection.JavaConverters._

object Conversions {
    def toFortressList[T](list: Seq[T]): fortress.data.ImmutableList[T] = 
        ImmutableWrapperList.copyCollection(list.asJava)
}
