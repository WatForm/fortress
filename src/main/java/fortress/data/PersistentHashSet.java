package fortress.data;

import java.util.stream.Stream;
import java.util.Iterator;
import java.lang.Iterable;
import java.util.Collection;
import java.util.Set;
import cyclops.data.HashSet;

public class PersistentHashSet<E> implements PersistentSet<E> {
    private final HashSet<E> implSet;
    
    private PersistentHashSet(HashSet<E> implSet) {
        this.implSet = implSet;
    }
    
    // New operations
    public static PersistentHashSet empty() {
        return new PersistentHashSet<>(HashSet.empty());
    }
    
    // PersistentSet operations
    @Override
    public PersistentSet<E> plus(E item) {
        return new PersistentHashSet<>(implSet.plus(item));
    }
    
    public PersistentSet<E> plusAll(Iterable<? extends E> iterable) {
        return new PersistentHashSet<>(implSet.plusAll(iterable));
    }
    
    @Override
    public boolean containsValue(E value) {
        return implSet.containsValue(value);
    }
    
    // Set operations
    
    // TODO inefficient
    @Override
    public boolean contains(Object o) {
        for(E item : implSet) {
            if(item.equals(o)) {
                return true;
            }
        }
        return false;
    }
    
    // TODO inefficient
    @Override
    public boolean containsAll(Collection<?> c) {
        for(Object item : c) {
            if(!contains(item)) {
                return false;
            }
        }
        return true;
    }
    
    @Override
    public boolean equals(Object o) {
        return (o instanceof Set)
                && ((Set) o).size() == size()
                && containsAll((Set) o);
    }
    
    @Override
    public int hashCode() {
        return implSet.hashCode();
    }
    
    @Override
    public boolean isEmpty() {
        return implSet.isEmpty();
    }
    
    @Override
    public Iterator<E> iterator() {
        return implSet.iterator();
    }
    
    @Override
    public int size() {
        return implSet.size();
    }
    
    @Override
    public Stream<E> stream() {
        return implSet.stream();
    }
    
    @Override
    public Object[] toArray() {
        return implSet.toArray();
    }
    
    // TODO must implement
    @Override
    public <T> T[] toArray(T[] as) {
        throw new UnsupportedOperationException("PersistentHashSet<E> does not support <T> T[] toArray(T[] a) at this time. It will be implemented.");
    } 
    
    @Override
    public String toString() {
        return implSet.toString();
    }
}
