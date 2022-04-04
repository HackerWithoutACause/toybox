pub trait MapInVec<T> {
    fn map<O, F>(self, _: F) -> Vec<O>
    where
        F: FnMut(T) -> O;
    fn map_ref<O, F>(&self, _: F) -> Vec<O>
    where
        F: FnMut(&T) -> O;
}

impl<T> MapInVec<T> for Vec<T> {
    fn map<O, F>(self, f: F) -> Vec<O>
    where
        F: FnMut(T) -> O,
    {
        self.into_iter().map(f).collect()
    }

    fn map_ref<O, F>(&self, f: F) -> Vec<O>
    where
        F: FnMut(&T) -> O,
    {
        self.iter().map(f).collect()
    }
}
