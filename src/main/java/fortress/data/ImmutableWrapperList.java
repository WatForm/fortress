package fortress.data;

import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Collection;
import java.util.function.Function;

// Wraps a standard list but provides no mutation operators
// NOTE: this differs from a stanard Java unmodifiable view, because there
// is no way for a user to access the underlying list and modify it without
// going through the view
public class ImmutableWrapperList<E> implements ImmutableList<E> {
    private final List<E> implList;
    
    protected ImmutableWrapperList(List<E> implList) {
        this.implList = implList;
    }
    
    // New operations
    
    // Shallow copy
    public static <T> ImmutableWrapperList<T> copyCollection(Collection<T> collection) {
        return new ImmutableWrapperList(new ArrayList<T>(collection));
    }
    
    // Shallow copy
    public static <T> ImmutableWrapperList<T> copyArray(T[] array) {
        return new ImmutableWrapperList(new ArrayList<T>(Arrays.asList(array)));
    }
    
    // List operations
    @Override
    public boolean contains(Object o) {
        return implList.contains(o);
    }
    
    @Override
    public boolean containsAll(Collection<?> c) {
        return implList.containsAll(c);
    }
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof List)) {
            return false;
        }
        List oList = (List) o;
        if(oList.size() != size()) {
            return false;
        }
        Iterator<E> thisIterator = iterator();
        Iterator thatIterator = oList.iterator();
        while(thisIterator.hasNext() && thatIterator.hasNext()) {
            if(!thisIterator.next().equals(thatIterator.next())) {
                return false;
            }
        }
        return true;
    }
    
    @Override
    public E get(int index) {
        return implList.get(index);
    }
    
    @Override
    public int hashCode() {
        return implList.hashCode();
    }
    
    @Override
    public int indexOf(Object o) {
        return implList.indexOf(o);
    }
    
    @Override
    public boolean isEmpty() {
        return implList.isEmpty();
    }
    
    @Override
    public Iterator<E> iterator() {
        return implList.iterator();
    }
    
    @Override
    public int lastIndexOf(Object o) {
        return implList.lastIndexOf(o);
    }
    
    @Override
    public ListIterator<E> listIterator() {
        return implList.listIterator();
    }
    
    @Override
    public ListIterator<E> listIterator(int index) {
        return implList.listIterator(index);
    }
    
    @Override
    public int size() {
        return implList.size();
    }
    
    @Override
    public ImmutableList<E> subList(int fromIndex, int toIndex) {
        List<E> sub = implList.subList(fromIndex, toIndex);
        return new ImmutableWrapperList(sub);
    }
    
    @Override
    public Object[] toArray() {
        return implList.toArray();
    }
    
    @Override
    public <T> T[] toArray(T[] as) {
        return implList.toArray(as);
    }
    
    @Override
    public String toString() {
        return implList.toString();
    }
    
    // ImmutableList operations
    @Override
    public <R> ImmutableList<R> map(Function<? super E, ? extends R> mapping) {
        List<R> newImplList = new ArrayList(implList.size());
        for(E elem : implList) {
            newImplList.add(mapping.apply(elem));
        }
        return new ImmutableWrapperList(newImplList);
    }
}
