package fortress.data

/**
  * Creates an object.
  */
trait Factory[A, I] {
    def create(arg: I): A
}

/**
  * Mixin trait which keeps a global cache for object creation.
  */
trait Caching[A <: AnyRef, I] extends Factory[A, I] {
    import scala.collection.mutable
    import scala.ref.WeakReference
    private val cache = mutable.Map.empty[I, ref.WeakReference[A]]

    abstract override def create(arg: I): A = synchronized {    
        cache.get(arg) match {
            case Some(WeakReference(cachedObject)) => cachedObject
            case _ => {
                val obj: A = super.create(arg)
                cache.put(arg, WeakReference(obj))
                obj
            }
        }
    }
}

class ConcreteFactory[A, I](private val createObject: I => A) extends Factory[A, I] {
    override def create(arg: I): A = createObject(arg)
}