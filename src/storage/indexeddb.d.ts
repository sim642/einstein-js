// https://stackoverflow.com/questions/42592104/missing-type-definition-for-idbobjectstore-getall
// https://developer.mozilla.org/en-US/docs/Web/API/IDBObjectStore/getAll

interface IDBObjectStore {
    getAll(): IDBRequest;
}