import { ipcMain } from 'electron';

const http = require('http');

function parseQueryString(req) {
  return new URL(req.url, `http://${req.headers.host}`);
}

export default {
  launch: function (win) {
    // Create a local server to receive data from
    const server = http.createServer((req, res) => {
      let data = '';
      req.on('data', chunk => {
        data += chunk;
      });
      req.on('end', () => {
        let rcode, body;
        let query = parseQueryString(req);
        switch (query.pathname) {
          case "/action":
            let goal = data;
            win.webContents.send('action', goal);
            ipcMain.on('action', (_, actionb, subgoalIndex) => {
              rcode = 200;
              res.writeHead(rcode, { 'Content-Type': 'text/plain' });
              res.end(subgoalIndex + "\n" + actionb);
            });
            ipcMain.on('done', _ => {
              rcode = 201;
              res.writeHead(rcode, { 'Content-Type': 'text/plain' });
              res.end('');
            });
            ipcMain.on('error', (_, msg) => {
              rcode = 550;
              res.writeHead(rcode, { 'Content-Type': 'text/plain' });
              res.end(msg);
            });
            break;
          default:
            rcode = 501;
            body = req.url;
            break;
        }
      });
    });
    server.listen(8124, () => {
      console.log('server bound');
    });
  }
}
