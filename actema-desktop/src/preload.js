import { contextBridge, ipcRenderer } from 'electron'

// Expose protected methods that allow the renderer process to use
// the ipcRenderer without exposing the entire object
contextBridge.exposeInMainWorld('ipcRenderer', {
  send: (channel, message) => ipcRenderer.send(channel, message),
  on: (channel, recv) => ipcRenderer.on(channel, recv)
})
