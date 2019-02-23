package fortress.data;

import java.util.function.Function;
import java.lang.Iterable;
import java.util.stream.Stream;
import java.util.Set;
import java.lang.UnsupportedOperationException;
import java.util.Collection;


public interface PersistentSet<E> extends Set<E> {
    
    // Unsupported Operations
    
    @Override
    default public boolean add(E value) {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the add operation");
    }
    
    @Override
    default public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the addAll operation");
    }
    
    @Override
    default public void clear() {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the clear operation");
    }
    
    @Override
    default public boolean remove(Object o) {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the remove operation");
    }
    
    @Override
    default public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the removeAll operation");
    }
    
    @Override
    default public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("PersistentSet<E> does not support the retainAll operation");
    }
    
    // New operations
   
    public PersistentSet<E> plus(E value);
    
    public PersistentSet<E> minus(E value);
    
    // Added so users can be more confident in type safety
    public boolean containsValue(E value);
    
}
