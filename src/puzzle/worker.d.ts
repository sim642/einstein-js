// TODO: make new not require as any

declare module "*.worker.ts" {
    class WebpackWorker extends Worker {
        constructor();
    }

    export default WebpackWorker;
}