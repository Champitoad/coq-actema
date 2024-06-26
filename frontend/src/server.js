import { ipcMain } from 'electron';

const http = require('http');

function parseQueryString(req) {
  return new URL(req.url, `http://${req.headers.host}`);
}

export default {
  launch: function (win) {
    // Create a local server that receives requests from the plugin.
    const server = http.createServer((req, res) => {
      ipcMain.removeAllListeners('request_lemmas');
      ipcMain.removeAllListeners('action');
      ipcMain.removeAllListeners('done');
      ipcMain.removeAllListeners('undo');
      ipcMain.removeAllListeners('redo');
      ipcMain.removeAllListeners('error');

      ipcMain.once('action', (_, action) => {
        let rcode = 200;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end(action.subgoalIndex.toString() + "\n" + action.repr);
      });
      ipcMain.once('done', _ => {
        let rcode = 251;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      ipcMain.once('undo', _ => {
        let rcode = 252;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      ipcMain.once('redo', _ => {
        let rcode = 253;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end('');
      });
      // Request lemmas to the backend.
      ipcMain.once('request_lemmas', (_, msg) => {
        let rcode = 254;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end(msg);
      });

      ipcMain.once('error', (_, msg) => {
        let rcode = 550;
        res.writeHead(rcode, { 'Content-Type': 'text/plain' });
        res.end(msg);
      });

      let data = '';
      req.on('data', chunk => {
        data += chunk;
      });
      req.on('end', () => {
        let rcode, body;
        let query = parseQueryString(req);
        switch (query.pathname) {
          case "/lemmas":
            // The backend sent lemmas to us.
            win.webContents.send('received_lemmas', data);
            break;
          case "/action":
            let goals = data;
            win.webContents.send('action', goals);
            break;
          case "/qed":
            win.webContents.send('qed', '');
            rcode = 200;
            res.writeHead(rcode, { 'Content-Type': 'text/plain' });
            res.end('');
            break;
          case "/error":
            win.webContents.send('error', data);
            res.end('');
            break;
          default:
            rcode = 501;
            body = req.url;
            res.writeHead(rcode, { 'Content-Type': 'text/plain' });
            res.end(body);
            break;
        }
      });
    });
    server.listen(8124, () => {
      console.log('server bound');
    });
  }
}
